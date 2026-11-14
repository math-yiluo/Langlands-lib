import Langlands.Representation.Geometric.IntersectionLeviModulusBalance
import Langlands.AllField.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.AllField.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
import Langlands.AllField.Representation.Geometric.IntersectionLeviDiagonalCharacter
/-! The block-normalization balance of the explicit moduli on the intersection Levi. -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicStandardIntersectionsTheorem refinedLeviModulus_of_diagonal
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

section RootProducts

private theorem prod_subtype_ite
    {ι A : Type*} [Fintype ι] [CommMonoid A]
    (p : ι → Prop) [DecidablePred p] (a : ι → A) :
    (∏ i : {i // p i}, a i) = ∏ i, if p i then a i else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) a).symm

end RootProducts

universe uF

section Moduli

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The explicit block modulus of a diagonal element is the product of its
root quotients over pairs of coordinates in increasing blocks. -/
theorem leviModulus_of_diagonal {n : ℕ} (D : BlockShape n) (x : D.Levi F)
    (t : Fin n → Fˣ)
    (hx : (D.leviEmbedding F x : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun a => (t a : F))) :
    T.leviModulus D x =
      ∏ ab : {ab : Fin n × Fin n // blockIndex D ab.1 < blockIndex D ab.2},
        T.normalizedAbsUnits (t ab.1.1) / T.normalizedAbsUnits (t ab.1.2) := by
  classical
  set u : Fin n → ℝ≥0ˣ := fun a => T.normalizedAbsUnits (t a) with hu
  have hdet (i : Fin D.length) :
      T.determinantNorm (D.size i) (x i) = ∏ a, u (D.index i a) := by
    have hd : GeneralLinear.determinant (x i) = ∏ a, t (D.index i a) := by
      apply Units.ext
      rw [Units.coe_prod]
      change Matrix.det ((x i : GeneralLinear (D.size i) F) :
        Matrix (Fin (D.size i)) (Fin (D.size i)) F) = _
      rw [levi_block_diagonal D x t hx i, Matrix.det_diagonal]
    change T.normalizedAbsUnits (GeneralLinear.determinant (x i)) = _
    rw [hd, map_prod]
  rw [T.leviModulus_apply]
  simp only [hdet]
  calc
    _ = ∏ i : Fin D.length, ∏ j : Fin D.length, ∏ a : Fin (D.size i),
        ∏ b : Fin (D.size j),
          if i < j then u (D.index i a) / u (D.index j b) else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · simp only [hij, ite_true]
        symm
        simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Finset.prod_pow]
      · simp [hij]
    _ = ∏ i : Fin D.length, ∏ a : Fin (D.size i), ∏ j : Fin D.length,
        ∏ b : Fin (D.size j),
          if i < j then u (D.index i a) / u (D.index j b) else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      exact Finset.prod_comm
    _ = ∏ pq : D.Index × D.Index,
        if pq.1.1 < pq.2.1 then u (D.indexEquiv pq.1) / u (D.indexEquiv pq.2) else 1 := by
      rw [Fintype.prod_prod_type]
      simp only [Fintype.prod_sigma]
      rfl
    _ = ∏ ab : Fin n × Fin n,
        if blockIndex D ab.1 < blockIndex D ab.2 then u ab.1 / u ab.2 else 1 := by
      refine Fintype.prod_equiv (Equiv.prodCongr D.indexEquiv D.indexEquiv) _ _
        fun pq => ?_
      simp [blockIndex]
    _ = _ := (prod_subtype_ite
      (fun ab : Fin n × Fin n => blockIndex D ab.1 < blockIndex D ab.2)
      (fun ab => u ab.1 / u ab.2)).symm

/-- The explicit refined modulus of a diagonal element, when the inner blocks
compare as a function `g` of the standard coordinates. -/
theorem refinedLeviModulus_of_diagonal {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {γ : Type*} [LinearOrder γ] (g : Fin n → γ)
    (hS : ∀ i (a b : Fin (B.size i)), blockIndex (S i) a < blockIndex (S i) b ↔
      g (B.index i a) < g (B.index i b))
    (s : refinedLevi F B S) (t : Fin n → Fˣ)
    (hs : (B.leviEmbedding F s.val : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun a => (t a : F))) :
    T.refinedLeviModulus B S s =
      ∏ ab : {ab : Fin n × Fin n // blockIndex B ab.1 = blockIndex B ab.2 ∧
          g ab.1 < g ab.2},
        T.normalizedAbsUnits (t ab.1.1) / T.normalizedAbsUnits (t ab.1.2) := by
  classical
  set u : Fin n → ℝ≥0ˣ := fun a => T.normalizedAbsUnits (t a) with hu
  have hblock (i : Fin B.length) :
      T.leviModulus (S i) (Langlands.LocalFieldData.refinedLeviBlock B S i s) =
        ∏ cd : Fin (B.size i) × Fin (B.size i),
          if g (B.index i cd.1) < g (B.index i cd.2) then
            u (B.index i cd.1) / u (B.index i cd.2) else 1 := by
    have he : ((S i).leviEmbedding F
        (Langlands.LocalFieldData.refinedLeviBlock B S i s) :
          Matrix (Fin (B.size i)) (Fin (B.size i)) F) =
        Matrix.diagonal (fun a => (t (B.index i a) : F)) := by
      have h₁ : (S i).leviEmbedding F
          (Langlands.LocalFieldData.refinedLeviBlock B S i s) = s.val i :=
        congrArg Subtype.val (((S i).leviEquiv F).apply_symm_apply
          (refinedLeviEval F B S i s))
      rw [h₁]
      exact levi_block_diagonal B s.val t hs i
    rw [leviModulus_of_diagonal T (S i) _ (fun a => t (B.index i a)) he,
      prod_subtype_ite
        (fun cd : Fin (B.size i) × Fin (B.size i) =>
          blockIndex (S i) cd.1 < blockIndex (S i) cd.2)
        (fun cd => u (B.index i cd.1) / u (B.index i cd.2))]
    simp only [hS]
  rw [T.refinedLeviModulus_apply]
  simp only [hblock]
  rw [prod_subtype_ite
    (fun ab : Fin n × Fin n => blockIndex B ab.1 = blockIndex B ab.2 ∧ g ab.1 < g ab.2)
    (fun ab => u ab.1 / u ab.2)]
  exact prod_within_blocks B (fun a b => g a < g b) (fun a b => u a / u b)

end Moduli

/-- The block-normalization balance on the actual intersection Levi
`M ∩ w⁻¹ N w`. For `m` there, with `m'` its conjugate in `N ∩ w M w⁻¹`, the
explicit moduli of `B`, of `C` and of the two Levi-intersection refinements
satisfy `δ_B(m) δ_C(m') δ_{B,S}(m) = δ_{C,R}(m') ε(m')²`, where `ε` is the actual
Haar modulus of `V ∩ w P w⁻¹`. Each modulus is evaluated at any coordinate
element with the same underlying matrix. -/
theorem intersectionLeviModulusBalance
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B C : BlockShape n) (w : MinimalRepresentatives B C)
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w.val = refinedLevi F B S)
    (hR : sourceLevi F C B w.val⁻¹ = refinedLevi F C R) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    let M := B.leviSubgroup F
    let N := C.leviSubgroup F
    let V := C.unipotentSubgroup F
    let P := B.parabolic F
    let g := GeneralLinear.permutation n F w.val
    let hV := C.isClosed_unipotentSubgroup F
    let hP := B.isClosed_parabolic F
    let hNV := C.leviSubgroup_le_normalizer_unipotentSubgroup F
    let hMP : M ≤ Subgroup.normalizer P := fun x hx =>
      P.le_normalizer (B.leviAsParabolic F ⟨x, hx⟩).property
    ∀ (m : General.intersectionIn M N g) (x : B.Levi F) (y : C.Levi F)
      (s : refinedLevi F B S) (r : refinedLevi F C R),
      B.leviEmbedding F x = m.val.val →
      C.leviEmbedding F y = (General.intersectionEquiv M N g m).val.val →
      B.leviEmbedding F s.val = m.val.val →
      C.leviEmbedding F r.val = (General.intersectionEquiv M N g m).val.val →
      T.leviModulus B x * T.leviModulus C y * T.refinedLeviModulus B S s =
        T.refinedLeviModulus C R r *
          General.intersectionCorrectionModulus N M V P g⁻¹ hV hP hNV hMP
            (General.intersectionEquiv M N g m) ^ 2 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro M N V P g hV hP hNV hMP
  have hScmp := refinement_lt_iff_of_sourceLevi F B C w.val w.property.1 S hS
  have hRcmp := refinement_lt_iff_of_sourceLevi F C B w.val⁻¹ w.property.2 R hR
  let I := General.intersectionIn M N g
  let J := General.intersectionIn N M g⁻¹
  let e := General.intersectionEquiv M N g
  let κB : I →* B.Levi F :=
    (B.leviEquiv F).symm.toMonoidHom.comp I.subtype
  let κC : I →* C.Levi F :=
    ((C.leviEquiv F).symm.toMonoidHom.comp J.subtype).comp e.toMonoidHom
  have hκB (m : I) : B.leviEmbedding F (κB m) = m.val.val :=
    congrArg Subtype.val ((B.leviEquiv F).apply_symm_apply m.val)
  have hκC (m : I) : C.leviEmbedding F (κC m) = (e m).val.val :=
    congrArg Subtype.val ((C.leviEquiv F).apply_symm_apply (e m).val)
  have hκS (m : I) : κB m ∈ refinedLevi F B S := by
    rw [← hS]
    change GeneralLinear.permutation n F w.val * B.leviEmbedding F (κB m) *
      (GeneralLinear.permutation n F w.val)⁻¹ ∈ C.leviSubgroup F
    rw [hκB]
    exact m.property
  have hκR (m : I) : κC m ∈ refinedLevi F C R := by
    rw [← hR]
    change GeneralLinear.permutation n F w.val⁻¹ * C.leviEmbedding F (κC m) *
      (GeneralLinear.permutation n F w.val⁻¹)⁻¹ ∈ B.leviSubgroup F
    rw [hκC, map_inv]
    exact (e m).property
  let κS : I →* refinedLevi F B S := κB.codRestrict _ hκS
  let κR : I →* refinedLevi F C R := κC.codRestrict _ hκR
  let ε : J →* ℝ≥0ˣ := General.intersectionCorrectionModulus N M V P g⁻¹ hV hP hNV hMP
  let ψ₁ : I →* ℝ≥0ˣ :=
    (T.leviModulus B).comp κB * (T.leviModulus C).comp κC *
      (T.refinedLeviModulus B S).comp κS
  let ψ₂ : I →* ℝ≥0ˣ :=
    (T.refinedLeviModulus C R).comp κR * (ε.comp e.toMonoidHom * ε.comp e.toMonoidHom)
  have hψ (m : I) : ψ₁ m = ψ₂ m := by
    have hχ := intersectionLeviDiagonalCharacter F (exists_ne_zero_ne_one F) n B C w
      (Jacquet.complexCharacter (ψ₁ / ψ₂)) ?_ m
    · have h := congrArg Units.val hχ
      rw [Jacquet.complexCharacter_apply] at h
      have h' : ((ψ₁ / ψ₂) m : ℝ≥0) = 1 :=
        NNReal.coe_eq_one.mp (Complex.ofReal_eq_one.mp h)
      have h'' : (ψ₁ / ψ₂) m = 1 := Units.ext h'
      exact div_eq_one.mp h''
    intro t m₀ hm
    let u : Fin n → ℝ≥0ˣ := fun a => T.normalizedAbsUnits (t a)
    let t' : Fin n → Fˣ := fun i => t (w.val.symm i)
    have hm' : ((e m₀).val.val : Matrix (Fin n) (Fin n) F) =
        Matrix.diagonal (fun i => (t' i : F)) :=
      General.intersectionEquiv_diagonal B C w.val t m₀ hm
    have hB : (B.leviEmbedding F (κB m₀) : Matrix (Fin n) (Fin n) F) =
        Matrix.diagonal (fun i => (t i : F)) := by
      rw [hκB]
      exact hm
    have hC : (C.leviEmbedding F (κC m₀) : Matrix (Fin n) (Fin n) F) =
        Matrix.diagonal (fun i => (t' i : F)) := by
      rw [hκC]
      exact hm'
    have hδB := leviModulus_of_diagonal T B (κB m₀) t hB
    have hδC := leviModulus_of_diagonal T C (κC m₀) t' hC
    have hδS := refinedLeviModulus_of_diagonal T B S (fun a => blockIndex C (w.val a))
      hScmp (κS m₀) t hB
    have hδR := refinedLeviModulus_of_diagonal T C R (fun c => blockIndex B (w.val⁻¹ c))
      hRcmp (κR m₀) t' hC
    have hεspec := correctionSubgroupDiagonalHaar F T n C B w.val⁻¹
    dsimp only at hεspec
    rw! [map_inv] at hεspec
    have hε := hεspec t'
      (General.intersectionToCorrectionNormalizer N M V P g⁻¹ hNV hMP (e m₀)) hm'
    change ε (e m₀) = _ at hε
    have hbal : ψ₁ m₀ = ψ₂ m₀ := by
      change T.leviModulus B (κB m₀) * T.leviModulus C (κC m₀) *
          T.refinedLeviModulus B S (κS m₀) =
        T.refinedLeviModulus C R (κR m₀) * (ε (e m₀) * ε (e m₀))
      rw [hδB, hδC, hδS, hδR, hε, ← pow_two]
      rw [prod_pairs_reindex_iff w.val
          (fun cd : Fin n × Fin n => blockIndex C cd.1 < blockIndex C cd.2)
          (fun ab : Fin n × Fin n =>
            blockIndex C (w.val ab.1) < blockIndex C (w.val ab.2))
          (fun _ => Iff.rfl) u,
        prod_pairs_reindex_iff w.val
          (fun cd : Fin n × Fin n => blockIndex C cd.1 = blockIndex C cd.2 ∧
            blockIndex B (w.val⁻¹ cd.1) < blockIndex B (w.val⁻¹ cd.2))
          (fun ab : Fin n × Fin n =>
            blockIndex C (w.val ab.1) = blockIndex C (w.val ab.2) ∧
              blockIndex B ab.1 < blockIndex B ab.2)
          (fun ab => by simp) u,
        prod_pairs_reindex_iff w.val
          (fun cd : Fin n × Fin n => blockIndex C cd.1 < blockIndex C cd.2 ∧
            blockIndex B (w.val⁻¹ cd.1) ≤ blockIndex B (w.val⁻¹ cd.2))
          (fun ab : Fin n × Fin n =>
            blockIndex C (w.val ab.1) < blockIndex C (w.val ab.2) ∧
              blockIndex B ab.1 ≤ blockIndex B ab.2)
          (fun ab => by simp) u]
      exact modulus_balance_root_products (blockIndex B)
        (fun a => blockIndex C (w.val a)) u
    have h1 : (ψ₁ / ψ₂) m₀ = 1 := div_eq_one.mpr hbal
    simp only [Jacquet.complexCharacter, MonoidHom.comp_apply, h1, map_one]
  intro m x y s r hx hy hs hr
  have hx' : x = κB m := B.leviEmbedding_injective F (hx.trans (hκB m).symm)
  have hy' : y = κC m := C.leviEmbedding_injective F (hy.trans (hκC m).symm)
  have hs' : s = κS m :=
    Subtype.ext (B.leviEmbedding_injective F (hs.trans (hκB m).symm))
  have hr' : r = κR m :=
    Subtype.ext (C.leviEmbedding_injective F (hr.trans (hκC m).symm))
  subst hx' hy' hs' hr'
  rw [pow_two]
  exact hψ m

/-- The same balance in the source-Levi coordinates: `m` in `M ∩ w⁻¹ N w` as a
subgroup of the product Levi of `B`, `m'` its conjugate in the product Levi of
`C`, the refined moduli evaluated through the Levi parts of the intersection
equalities, and the Haar modulus evaluated at the element of `N ∩ w M w⁻¹`
with the matrix of `m'`. -/
theorem intersectionLeviModulusBalance_sourceLevi
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B C : BlockShape n) (w : MinimalRepresentatives B C)
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w.val = refinedLevi F B S)
    (hR : sourceLevi F C B w.val⁻¹ = refinedLevi F C R) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    let M := B.leviSubgroup F
    let N := C.leviSubgroup F
    let V := C.unipotentSubgroup F
    let P := B.parabolic F
    let g := GeneralLinear.permutation n F w.val
    let hV := C.isClosed_unipotentSubgroup F
    let hP := B.isClosed_parabolic F
    let hNV := C.leviSubgroup_le_normalizer_unipotentSubgroup F
    let hMP : M ≤ Subgroup.normalizer P := fun x hx =>
      P.le_normalizer (B.leviAsParabolic F ⟨x, hx⟩).property
    ∀ (m : sourceLevi F B C w.val) (j : General.intersectionIn N M g⁻¹),
      j.val.val = C.leviEmbedding F
        (intersectionLeviConjugation F B C w.val m).val →
      T.leviModulus B m.val *
          T.leviModulus C (intersectionLeviConjugation F B C w.val m).val *
          T.refinedLeviModulus B S (MulEquiv.subgroupCongr hS m) =
        T.refinedLeviModulus C R
            (MulEquiv.subgroupCongr hR (intersectionLeviConjugation F B C w.val m)) *
          General.intersectionCorrectionModulus N M V P g⁻¹ hV hP hNV hMP j ^ 2 := by
  intro M N V P g hV hP hNV hMP m j hj
  let mI : General.intersectionIn M N g :=
    ⟨⟨B.leviEmbedding F m.val, m.val, rfl⟩, m.property⟩
  have he : General.intersectionEquiv M N g mI = j := by
    apply Subtype.ext
    apply Subtype.ext
    rw [General.intersectionEquiv_apply, hj, intersectionLeviConjugation_embedding]
  rw [← he]
  exact intersectionLeviModulusBalance F T n B C w S R hS hR mI m.val
    (intersectionLeviConjugation F B C w.val m).val
    (MulEquiv.subgroupCongr hS m)
    (MulEquiv.subgroupCongr hR (intersectionLeviConjugation F B C w.val m))
    rfl
    ((intersectionLeviConjugation_embedding F B C w.val m).trans
      (General.intersectionEquiv_apply M N g mI).symm)
    rfl
    ((intersectionLeviConjugation_embedding F B C w.val m).trans
      (General.intersectionEquiv_apply M N g mI).symm)

/-- The positive complex halves of the source-Levi balance: the three source and
target half moduli equal the refined target half modulus times the complex Haar
modulus of `V ∩ w P w⁻¹`. -/
theorem intersectionLeviHalfModulusBalance_sourceLevi
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B C : BlockShape n) (w : MinimalRepresentatives B C)
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F B C w.val = refinedLevi F B S)
    (hR : sourceLevi F C B w.val⁻¹ = refinedLevi F C R) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    let M := B.leviSubgroup F
    let N := C.leviSubgroup F
    let V := C.unipotentSubgroup F
    let P := B.parabolic F
    let g := GeneralLinear.permutation n F w.val
    let hV := C.isClosed_unipotentSubgroup F
    let hP := B.isClosed_parabolic F
    let hNV := C.leviSubgroup_le_normalizer_unipotentSubgroup F
    let hMP : M ≤ Subgroup.normalizer P := fun x hx =>
      P.le_normalizer (B.leviAsParabolic F ⟨x, hx⟩).property
    ∀ (m : sourceLevi F B C w.val) (j : General.intersectionIn N M g⁻¹),
      j.val.val = C.leviEmbedding F
        (intersectionLeviConjugation F B C w.val m).val →
      T.leviHalfModulus B m.val *
          T.leviHalfModulus C (intersectionLeviConjugation F B C w.val m).val *
          T.refinedLeviHalfModulus B S (MulEquiv.subgroupCongr hS m) =
        T.refinedLeviHalfModulus C R
            (MulEquiv.subgroupCongr hR (intersectionLeviConjugation F B C w.val m)) *
          Jacquet.complexCharacter
            (General.intersectionCorrectionModulus N M V P g⁻¹ hV hP hNV hMP) j := by
  intro M N V P g hV hP hNV hMP m j hj
  have h := congrArg (fun z : ℝ≥0ˣ => NNReal.sqrt (z : ℝ≥0))
    (intersectionLeviModulusBalance_sourceLevi F T n B C w S R hS hR m j hj)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, NNReal.sqrt_mul,
    NNReal.sqrt_sq] at h
  apply Units.ext
  simp only [Units.val_mul, T.leviHalfModulus_apply, T.refinedLeviHalfModulus_apply,
    Jacquet.complexCharacter_apply]
  exact_mod_cast h

end Langlands.AllField.Geometric
