import Langlands.Representation.Geometric.PadicCorrectionCancellationStatement
import Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
import Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual positive Haar correction cancellation for p-adic GL parabolic orbits. -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.Geometric

private theorem prod_subtype_eq_prod_ite
    {ι A : Type*} [Fintype ι] [CommMonoid A]
    (p : ι → Prop) [DecidablePred p] (a : ι → A) :
    (∏ i : {i // p i}, a i) = ∏ i, if p i then a i else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) a).symm

private theorem prod_pairs_reindex
    {ι κ A : Type*} [Fintype ι] [Fintype κ] [CommGroup A]
    (e : ι ≃ κ) (p : κ × κ → Prop) [DecidablePred p] (a : ι → A) :
    (∏ ij : {ij : κ × κ // p ij}, a (e.symm ij.1.1) / a (e.symm ij.1.2)) =
      ∏ ij : {ij : ι × ι // p (e ij.1, e ij.2)}, a ij.1.1 / a ij.1.2 := by
  rw [prod_subtype_eq_prod_ite p (fun ij => a (e.symm ij.1) / a (e.symm ij.2)),
    prod_subtype_eq_prod_ite (fun ij : ι × ι => p (e ij.1, e ij.2))
      (fun ij => a ij.1 / a ij.2)]
  apply Fintype.prod_equiv (Equiv.prodCongr e.symm e.symm)
  intro ij
  simp

/-- Opposite omitted roots have inverse weights, so the two full root products
equal the products on the two allowed correction patterns. -/
theorem correction_root_products
    {ι β γ A : Type*} [Fintype ι] [LinearOrder β] [LinearOrder γ] [CommGroup A]
    (f : ι → β) (g : ι → γ) (a : ι → A) :
    (∏ ij : {ij : ι × ι // f ij.1 < f ij.2}, a ij.1.1 / a ij.1.2) *
        (∏ ij : {ij : ι × ι // g ij.1 < g ij.2}, a ij.1.1 / a ij.1.2) =
      (∏ ij : {ij : ι × ι // f ij.1 < f ij.2 ∧ g ij.1 ≤ g ij.2},
          a ij.1.1 / a ij.1.2) *
        (∏ ij : {ij : ι × ι // g ij.1 < g ij.2 ∧ f ij.1 ≤ f ij.2},
          a ij.1.1 / a ij.1.2) := by
  classical
  let r : ι × ι → A := fun ij =>
    if f ij.1 < f ij.2 ∧ g ij.2 < g ij.1 then a ij.1 / a ij.2 else 1
  let s : ι × ι → A := fun ij =>
    if g ij.1 < g ij.2 ∧ f ij.2 < f ij.1 then a ij.1 / a ij.2 else 1
  have hf : (∏ ij : ι × ι, if f ij.1 < f ij.2 then a ij.1 / a ij.2 else 1) =
      (∏ ij : ι × ι,
        if f ij.1 < f ij.2 ∧ g ij.1 ≤ g ij.2 then a ij.1 / a ij.2 else 1) *
        ∏ ij : ι × ι, r ij := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ij _
    by_cases h : f ij.1 < f ij.2
    · by_cases h' : g ij.1 ≤ g ij.2
      · simp [r, h, h', not_lt.mpr h']
      · simp [r, h, h', lt_of_not_ge h']
    · simp [r, h]
  have hg : (∏ ij : ι × ι, if g ij.1 < g ij.2 then a ij.1 / a ij.2 else 1) =
      (∏ ij : ι × ι,
        if g ij.1 < g ij.2 ∧ f ij.1 ≤ f ij.2 then a ij.1 / a ij.2 else 1) *
        ∏ ij : ι × ι, s ij := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ij _
    by_cases h : g ij.1 < g ij.2
    · by_cases h' : f ij.1 ≤ f ij.2
      · simp [s, h, h', not_lt.mpr h']
      · simp [s, h, h', lt_of_not_ge h']
    · simp [s, h]
  have hrs : (∏ ij : ι × ι, r ij) * ∏ ij : ι × ι, s ij = 1 := by
    have hswap : (∏ ij : ι × ι, s ij) = ∏ ij : ι × ι, (r ij)⁻¹ := by
      apply Fintype.prod_equiv (Equiv.prodComm ι ι)
      intro ij
      by_cases h : g ij.1 < g ij.2 ∧ f ij.2 < f ij.1
      · simp [r, s, h.1, h.2]
      · have h' : ¬(f ij.2 < f ij.1 ∧ g ij.1 < g ij.2) := by tauto
        simp [r, s, h, h']
    rw [hswap, Finset.prod_inv_distrib]
    exact mul_inv_cancel _
  rw [prod_subtype_eq_prod_ite (fun ij : ι × ι => f ij.1 < f ij.2)
      (fun ij => a ij.1 / a ij.2),
    prod_subtype_eq_prod_ite (fun ij : ι × ι => g ij.1 < g ij.2)
      (fun ij => a ij.1 / a ij.2),
    prod_subtype_eq_prod_ite
      (fun ij : ι × ι => f ij.1 < f ij.2 ∧ g ij.1 ≤ g ij.2)
      (fun ij => a ij.1 / a ij.2),
    prod_subtype_eq_prod_ite
      (fun ij : ι × ι => g ij.1 < g ij.2 ∧ f ij.1 ≤ f ij.2)
      (fun ij => a ij.1 / a ij.2)]
  rw [hf, hg]
  calc
    _ = ((∏ ij : ι × ι,
          if f ij.1 < f ij.2 ∧ g ij.1 ≤ g ij.2 then a ij.1 / a ij.2 else 1) *
          ∏ ij : ι × ι,
          if g ij.1 < g ij.2 ∧ f ij.1 ≤ f ij.2 then a ij.1 / a ij.2 else 1) *
        ((∏ ij : ι × ι, r ij) * ∏ ij : ι × ι, s ij) := by ac_rfl
    _ = _ := by rw [hrs, mul_one]

/-- The finite root balance with the second pattern written in its own indices,
and with its weights transported by the inverse permutation. -/
theorem correction_root_products_reindex
    {ι κ β γ A : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder β] [LinearOrder γ] [CommGroup A]
    (e : ι ≃ κ) (f : ι → β) (g : κ → γ) (a : ι → A) :
    (∏ ij : {ij : ι × ι // f ij.1 < f ij.2}, a ij.1.1 / a ij.1.2) *
        (∏ ij : {ij : κ × κ // g ij.1 < g ij.2},
          a (e.symm ij.1.1) / a (e.symm ij.1.2)) =
      (∏ ij : {ij : ι × ι // f ij.1 < f ij.2 ∧ g (e ij.1) ≤ g (e ij.2)},
          a ij.1.1 / a ij.1.2) *
        (∏ ij : {ij : κ × κ // g ij.1 < g ij.2 ∧
            f (e.symm ij.1) ≤ f (e.symm ij.2)},
          a (e.symm ij.1.1) / a (e.symm ij.1.2)) := by
  classical
  let E :
      {ij : κ × κ // g ij.1 < g ij.2 ∧ f (e.symm ij.1) ≤ f (e.symm ij.2)} ≃
        {ij : ι × ι // g (e ij.1) < g (e ij.2) ∧ f ij.1 ≤ f ij.2} :=
    { toFun ij := ⟨(e.symm ij.1.1, e.symm ij.1.2), by simpa using ij.property⟩
      invFun ij := ⟨(e ij.1.1, e ij.1.2), by simpa using ij.property⟩
      left_inv ij := by apply Subtype.ext; simp
      right_inv ij := by apply Subtype.ext; simp }
  have hsecond :
      (∏ ij : {ij : κ × κ // g ij.1 < g ij.2 ∧
          f (e.symm ij.1) ≤ f (e.symm ij.2)},
        a (e.symm ij.1.1) / a (e.symm ij.1.2)) =
      ∏ ij : {ij : ι × ι // g (e ij.1) < g (e ij.2) ∧ f ij.1 ≤ f ij.2},
        a ij.1.1 / a ij.1.2 :=
    Fintype.prod_equiv E _ _ (fun _ => rfl)
  rw [prod_pairs_reindex e (fun ij => g ij.1 < g ij.2) a, hsecond]
  exact correction_root_products f (fun i => g (e i)) a

/-- The positive half construction carries a balanced product of positive
moduli to exact cancellation in the complex units. -/
theorem positive_half_corrections_cancel
    {H : Type*} [Group H] (δ₁ ε₁ δ₂ ε₂ : H →* ℝ≥0ˣ) (x : H)
    (h : δ₁ x * δ₂ x = ε₁ x * ε₂ x) :
    Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ₁) x *
        Jacquet.inverseHalfCharacter ε₁ x *
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ₂) x *
        Jacquet.inverseHalfCharacter ε₂ x) = 1 := by
  let φ : ℝ≥0ˣ →* ℂˣ :=
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp
      (Units.map NNReal.sqrtHom.toMonoidHom)
  change φ (δ₁ x) * (φ (ε₁ x))⁻¹ * (φ (δ₂ x) * (φ (ε₂ x))⁻¹) = 1
  calc
    _ = φ ((δ₁ x * δ₂ x) / (ε₁ x * ε₂ x)) := by
      simp only [map_mul, div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ = 1 := by rw [h, div_self', map_one]

namespace General

/-- The full correction subgroup specializes to the whole radical when the
other parabolic is its own and the conjugating element is the identity. -/
theorem intersectionSource_radical_self
    {R : Type*} [CommRing R] {n : ℕ} (B : GeneralLinear.BlockShape n) :
    intersectionSource (B.unipotentSubgroup R) (B.parabolic R)
      (GeneralLinear.permutation n R 1) = B.unipotentSubgroup R := by
  rw [map_one]
  ext u
  change (u ∈ B.unipotentSubgroup R ∧
    (1 : GeneralLinear n R) * u * 1⁻¹ ∈ B.parabolic R) ↔
      u ∈ B.unipotentSubgroup R
  simp only [inv_one, one_mul, mul_one]
  exact and_iff_left_of_imp (fun hu => ((B.mem_unipotentSubgroup_iff R u).mp hu).1)

/-- Actual conjugation through the intersection equivalence transports the
diagonal entries by the inverse permutation. -/
theorem intersectionEquiv_diagonal
    {R : Type*} [CommRing R] {n : ℕ}
    (B C : GeneralLinear.BlockShape n) (w : Equiv.Perm (Fin n))
    (t : Fin n → Rˣ)
    (m : intersectionIn (B.leviSubgroup R) (C.leviSubgroup R)
      (GeneralLinear.permutation n R w))
    (hm : (m.val.val : Matrix (Fin n) (Fin n) R) =
      Matrix.diagonal (fun i => (t i : R))) :
    ((intersectionEquiv (B.leviSubgroup R) (C.leviSubgroup R)
      (GeneralLinear.permutation n R w) m).val.val :
        Matrix (Fin n) (Fin n) R) =
      Matrix.diagonal (fun i => (t (w.symm i) : R)) := by
  classical
  ext i j
  change (GeneralLinear.permutation n R w * m.val.val *
    (GeneralLinear.permutation n R w)⁻¹) i j = _
  rw [GeneralLinear.permutation_conjugate_entry]
  change m.val.val (w.symm i) (w.symm j) = _
  have h := congrFun (congrFun hm (w.symm i)) (w.symm j)
  simpa only [Matrix.diagonal_apply, w.symm.injective.eq_iff] using h

/-- Assembly for the actual correction factors once the balanced product of the
four actual Haar moduli has been proved. This is an internal helper, not the
unconditional p-adic cancellation theorem. -/
theorem haar_corrections_cancel_of_modulus_products
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (M N U Q V P : Subgroup G) (w : G)
    (hU : IsClosed (U : Set G)) (hQ : IsClosed (Q : Set G))
    (hV : IsClosed (V : Set G)) (hP : IsClosed (P : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hNQ : N ≤ Subgroup.normalizer Q)
    (hNV : N ≤ Subgroup.normalizer V) (hMP : M ≤ Subgroup.normalizer P)
    (m : intersectionIn M N w)
    (h : intersectionRadicalModulus M N U w hU hMU m *
          intersectionRadicalModulus N M V w⁻¹ hV hNV (intersectionEquiv M N w m) =
        intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ m *
          intersectionCorrectionModulus N M V P w⁻¹ hV hP hNV hMP
            (intersectionEquiv M N w m)) :
    haarCorrectionCharacter M N U Q w hU hQ hMU hNQ m *
      haarCorrectionCharacter N M V P w⁻¹ hV hP hNV hMP
        (intersectionEquiv M N w m) = 1 := by
  exact positive_half_corrections_cancel
    (intersectionRadicalModulus M N U w hU hMU)
    (intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ)
    ((intersectionRadicalModulus N M V w⁻¹ hV hNV).comp
      (intersectionEquiv M N w).toMonoidHom)
    ((intersectionCorrectionModulus N M V P w⁻¹ hV hP hNV hMP).comp
      (intersectionEquiv M N w).toMonoidHom) m h

end General

universe uF

/-- Specializing the full correction formula to its own parabolic gives the
actual diagonal modulus on the whole radical. -/
theorem radical_diagonal_modulus
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (t : Fin n → F.Carrierˣ)
      (d : Subgroup.normalizer (B.unipotentSubgroup F.Carrier :
        Set (GeneralLinear n F.Carrier))),
      (d.val : Matrix (Fin n) (Fin n) F.Carrier) =
          Matrix.diagonal (fun i => (t i : F.Carrier)) →
        Langlands.HaarModulus.closedNormalizerCharacter
          (B.unipotentSubgroup F.Carrier) (B.isClosed_unipotentSubgroup F.Carrier) d =
          ∏ ab : {ab : Fin n × Fin n // blockIndex B ab.1 < blockIndex B ab.2},
            T.normalizedAbsUnits (t ab.1.1) / T.normalizedAbsUnits (t ab.1.2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro t d hd
  have h := correctionSubgroupDiagonalHaar p F T n B B 1
  dsimp only at h
  rw! [General.intersectionSource_radical_self] at h
  have htd := h t d hd
  let E :
      {ab : Fin n × Fin n // blockIndex B ab.1 < blockIndex B ab.2 ∧
        blockIndex B ab.1 ≤ blockIndex B ab.2} ≃
      {ab : Fin n × Fin n // blockIndex B ab.1 < blockIndex B ab.2} :=
    { toFun ab := ⟨ab.val, ab.property.1⟩
      invFun ab := ⟨ab.val, ab.property, ab.property.le⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact htd.trans (Fintype.prod_equiv E _ _ (fun _ => rfl))

/-- Assembly using the published actual Haar formula, conditional only on
character determination on the intersection Levi. -/
theorem padicHaarCorrectionCancellation_of_diagonal_character
    (hChar : IntersectionLeviDiagonalCharacterStatement.{uF}) :
    PadicHaarCorrectionCancellation.{uF} := by
  intro p hp F T n _ B C w
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let M := B.leviSubgroup F.Carrier
  let N := C.leviSubgroup F.Carrier
  let U := B.unipotentSubgroup F.Carrier
  let V := C.unipotentSubgroup F.Carrier
  let P := B.parabolic F.Carrier
  let Q := C.parabolic F.Carrier
  let g := GeneralLinear.permutation n F.Carrier w.val
  let hU := B.isClosed_unipotentSubgroup F.Carrier
  let hV := C.isClosed_unipotentSubgroup F.Carrier
  let hP := B.isClosed_parabolic F.Carrier
  let hQ := C.isClosed_parabolic F.Carrier
  let hMU := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
  let hNV := C.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
  let hNQ : N ≤ Subgroup.normalizer Q := fun x hx =>
    Q.le_normalizer (C.leviAsParabolic F.Carrier ⟨x, hx⟩).property
  let hMP : M ≤ Subgroup.normalizer P := fun x hx =>
    P.le_normalizer (B.leviAsParabolic F.Carrier ⟨x, hx⟩).property
  let χ : General.intersectionIn M N g →* ℂˣ :=
    General.haarCorrectionCharacter M N U Q g hU hQ hMU hNQ *
      (General.haarCorrectionCharacter N M V P g⁻¹ hV hP hNV hMP).comp
        (General.intersectionEquiv M N g).toMonoidHom
  change ∀ m, χ m = 1
  refine hChar F.Carrier n B C w χ ?_
  intro t m hm
  change General.haarCorrectionCharacter M N U Q g hU hQ hMU hNQ m *
    General.haarCorrectionCharacter N M V P g⁻¹ hV hP hNV hMP
      (General.intersectionEquiv M N g m) = 1
  apply General.haar_corrections_cancel_of_modulus_products M N U Q V P g
    hU hQ hV hP hMU hNQ hNV hMP m
  let m' := General.intersectionEquiv M N g m
  let t' : Fin n → F.Carrierˣ := fun i => t (w.val.symm i)
  have hm' : (m'.val.val : Matrix (Fin n) (Fin n) F.Carrier) =
      Matrix.diagonal (fun i => (t' i : F.Carrier)) :=
    General.intersectionEquiv_diagonal B C w.val t m hm
  have hδ₁ := radical_diagonal_modulus p F T n B t
    (General.intersectionToRadicalNormalizer M N U g hMU m) hm
  change General.intersectionRadicalModulus M N U g hU hMU m = _ at hδ₁
  have hδ₂ := radical_diagonal_modulus p F T n C t'
    (General.intersectionToRadicalNormalizer N M V g⁻¹ hNV m') hm'
  change General.intersectionRadicalModulus N M V g⁻¹ hV hNV m' = _ at hδ₂
  have hε₁ := correctionSubgroupDiagonalHaar p F T n B C w.val t
    (General.intersectionToCorrectionNormalizer M N U Q g hMU hNQ m) hm
  change General.intersectionCorrectionModulus M N U Q g hU hQ hMU hNQ m = _ at hε₁
  have hε₂spec := correctionSubgroupDiagonalHaar p F T n C B w.val⁻¹
  dsimp only at hε₂spec
  rw! [map_inv] at hε₂spec
  have hε₂ := hε₂spec t'
    (General.intersectionToCorrectionNormalizer N M V P g⁻¹ hNV hMP m') hm'
  change General.intersectionCorrectionModulus N M V P g⁻¹ hV hP hNV hMP m' = _ at hε₂
  rw [hδ₁, hδ₂, hε₁, hε₂]
  exact correction_root_products_reindex w.val (blockIndex B) (blockIndex C)
    (fun i => T.normalizedAbsUnits (t i))

/-- The two actual positive Haar corrections cancel on the actual intersection
Levi, for every supplied compatible p-adic realization. -/
theorem padicHaarCorrectionCancellation :
    PadicHaarCorrectionCancellation.{uF} :=
  padicHaarCorrectionCancellation_of_diagonal_character
    intersectionLeviDiagonalCharacterTheorem

end Langlands.Geometric
