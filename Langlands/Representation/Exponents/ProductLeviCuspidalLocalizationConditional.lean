import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceConditional
import Langlands.Representation.Geometric.ProductLeviGeometricLemmaStatement
import Langlands.Representation.Exponents.WeylBranchPiecesStatement
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Geometric.RefinedOppositePieceMinimal
import Langlands.Representation.CuspidalSupport.ProperInductionProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof

/-!
# Product-Levi cuspidal localization from the product-Levi geometric lemma

The product-Levi geometric lemma (BZ77, 2.12, for the group `B.Levi`) implies
`GLProductLeviCuspidalLocalizationStatement`. This file proves that
implication; it does not prove the geometric lemma.
-/

noncomputable section

namespace Langlands.ProductLeviCuspidalLocalization

open GeneralLinear Geometric CuspidalSupport WeylBranchPieces CategoryTheory
open ProductLeviDualOpposite ProductLeviMinimalIndex Geometric.RefinedOppositePieceTransport
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uW uM

section Reversal

variable {m : ℕ}

/-- Inner reversal of a refinement is an involution. -/
theorem reverseRefinement_reverseRefinement (C : BlockShape m) (R : BlockRefinement C) :
    reverseRefinement C (reverseRefinement C R) = R :=
  funext fun j => GeometricExcessBranch.reverse_reverse (R j)

end Reversal

section Labels

variable {n : ℕ}

/-- Coordinates in blocks with increasing labels are increasing. -/
theorem lt_of_blockLabel_lt (X : BlockShape n) {a b : Fin n}
    (h : blockIndex X a < blockIndex X b) : a < b := by
  by_contra hba
  exact absurd (blockIndex_monotone X (not_lt.mp hba)) (not_le.mpr h)

/-- A block-diagonal permutation which reverses the order of refinement
blocks inside every coarse block reverses the order of two coordinates of one
coarse block lying in different refinement blocks. -/
theorem blockPermOf_lt_of_label_lt (X : BlockShape n) (S : BlockRefinement X)
    (τ : ∀ i, Equiv.Perm (Fin (X.size i)))
    (hτ : ∀ i (u v : Fin (X.size i)), blockIndex (S i) u < blockIndex (S i) v →
      τ i v < τ i u)
    {a b : Fin n} (hab : blockIndex X a = blockIndex X b)
    (hlt : blockIndex (X.flatten S) a < blockIndex (X.flatten S) b) :
    blockPermOf X τ b < blockPermOf X τ a := by
  obtain ⟨i, u, rfl⟩ := TotalConjugatingCount.index_surjective X a
  obtain ⟨i', v, rfl⟩ := TotalConjugatingCount.index_surjective X b
  have hi : i = i' := by simpa only [blockIndex_index] using hab
  subst i'
  have huv : u < v := (index_strictMono X i).lt_iff_lt.mp (lt_of_blockLabel_lt _ hlt)
  have hne : blockIndex (S i) u ≠ blockIndex (S i) v := fun h =>
    (ne_of_lt hlt) ((blockIndex_flatten_index_eq_iff X S i u v).mpr h)
  have hle : blockIndex (S i) u ≤ blockIndex (S i) v := blockIndex_monotone (S i) huv.le
  rw [blockPermOf_index, blockPermOf_index]
  exact index_strictMono X i (hτ i u v (lt_of_le_of_ne hle hne))

/-- The reversal permutation reverses the order of different reversed blocks. -/
theorem reversePermutation_lt_of_label_lt {m : ℕ} (E : BlockShape m) (u v : Fin m)
    (h : blockIndex E.reverse u < blockIndex E.reverse v) :
    E.reversePermutation v < E.reversePermutation u := by
  apply lt_of_blockLabel_lt E
  rw [blockIndex_reversePermutation, blockIndex_reversePermutation]
  exact Fin.rev_lt_rev.mpr h

/-- The inverse reversal permutation reverses the order of different blocks. -/
theorem reversePermutation_symm_lt_of_label_lt {m : ℕ} (E : BlockShape m) (u v : Fin m)
    (h : blockIndex E u < blockIndex E v) :
    E.reversePermutation.symm v < E.reversePermutation.symm u := by
  apply lt_of_blockLabel_lt E.reverse
  rw [blockIndex_reversePermutation_symm, blockIndex_reversePermutation_symm]
  exact Fin.rev_lt_rev.mpr h

/-- Inner reversal reverses the order of different reversed refinement blocks
inside one coarse block. -/
theorem innerReverse_lt_of_label_lt (B : BlockShape n) (S : BlockRefinement B)
    {a b : Fin n} (hab : blockIndex B a = blockIndex B b)
    (hlt : blockIndex (B.flatten (reverseRefinement B S)) a <
      blockIndex (B.flatten (reverseRefinement B S)) b) :
    innerReversePermutation B S b < innerReversePermutation B S a :=
  blockPermOf_lt_of_label_lt B (reverseRefinement B S) _
    (fun i u v h => reversePermutation_lt_of_label_lt (S i) u v h) hab hlt

/-- The inverse inner reversal reverses the order of different refinement
blocks inside one coarse block. -/
theorem innerReverse_symm_lt_of_label_lt (B : BlockShape n) (S : BlockRefinement B)
    {a b : Fin n} (hab : blockIndex B a = blockIndex B b)
    (hlt : blockIndex (B.flatten S) a < blockIndex (B.flatten S) b) :
    (innerReversePermutation B S).symm b < (innerReversePermutation B S).symm a := by
  unfold innerReversePermutation
  rw [blockPermOf_symm]
  exact blockPermOf_lt_of_label_lt B S _
    (fun i u v h => reversePermutation_symm_lt_of_label_lt (S i) u v h) hab hlt

variable (F : Type uF) [Field F]

/-- The localized permutation `x * (w * y⁻¹)`, with `x` the inner reversal of
the target refinement and `y` the inner reversal of the source refinement, is
a minimal representative for the source Levi and the original target. -/
theorem isMinimalRepresentative_localized {B : BlockShape n} (Q S : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) {w : Equiv.Perm (Fin n)} (hwB : w ∈ blockWeyl B)
    (hmin : IsMinimalRepresentative (B.flatten Q) (B.flatten (reverseRefinement B S)) w)
    (hw : ConjugatesLevi (F := F)
      ((B.flatten Q).flatten (reverseRefinement (B.flatten Q) R))
      (B.flatten (reverseRefinement B S)) w) :
    IsMinimalRepresentative (B.flatten Q) (B.flatten S)
      (innerReversePermutation B S *
        (w * (innerReversePermutation (B.flatten Q) R)⁻¹)) := by
  have hx := conjugatesLevi_innerReverse B S F
  have hy := conjugatesLevi_innerReverse (B.flatten Q) R F
  have hxmin := isMinimalRepresentative_innerReverse B S
  have hymin := isMinimalRepresentative_innerReverse (B.flatten Q) R
  rw [isMinimalRepresentative_iff] at hmin hxmin hymin ⊢
  have hyD : (innerReversePermutation (B.flatten Q) R)⁻¹ ∈ blockWeyl (B.flatten Q) :=
    (blockWeyl (B.flatten Q)).inv_mem (blockPermOf_mem_blockWeyl _ _)
  have hwB' : ∀ a, blockIndex B (w a) = blockIndex B a := hwB
  constructor
  · intro a b hab hlt
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    have hya : blockIndex (B.flatten Q) ((innerReversePermutation (B.flatten Q) R).symm a) =
        blockIndex (B.flatten Q) ((innerReversePermutation (B.flatten Q) R).symm b) :=
      ((hyD a).trans hab).trans (hyD b).symm
    by_cases hR : blockIndex ((B.flatten Q).flatten R) a =
      blockIndex ((B.flatten Q).flatten R) b
    · have h1 := hymin.2 a b hR hlt
      have h2 := (blockIndex_eq_iff_of_conjugatesLevi hy
        ((innerReversePermutation (B.flatten Q) R).symm a)
        ((innerReversePermutation (B.flatten Q) R).symm b)).mp
        (by simpa only [Equiv.apply_symm_apply] using hR)
      have h3 := hmin.1 _ _ hya h1
      have h4 := (blockIndex_eq_iff_of_conjugatesLevi hw _ _).mpr h2
      exact hxmin.1 _ _ h4 h3
    · have hRlt : blockIndex ((B.flatten Q).flatten R) a <
          blockIndex ((B.flatten Q).flatten R) b :=
        lt_of_le_of_ne (blockIndex_monotone _ hlt.le) hR
      have h1 := innerReverse_symm_lt_of_label_lt (B.flatten Q) R hab hRlt
      have h3 := hmin.1 _ _ hya.symm h1
      have hne : blockIndex (B.flatten (reverseRefinement B S))
            (w ((innerReversePermutation (B.flatten Q) R).symm b)) ≠
          blockIndex (B.flatten (reverseRefinement B S))
            (w ((innerReversePermutation (B.flatten Q) R).symm a)) := by
        intro h
        apply hR
        have h' := (blockIndex_eq_iff_of_conjugatesLevi hw _ _).mp h
        have h'' := (blockIndex_eq_iff_of_conjugatesLevi hy _ _).mpr h'
        simpa only [Equiv.apply_symm_apply] using h''.symm
      have h4 := lt_of_le_of_ne (blockIndex_monotone _ h3.le) hne
      have hBB : blockIndex B (w ((innerReversePermutation (B.flatten Q) R).symm b)) =
          blockIndex B (w ((innerReversePermutation (B.flatten Q) R).symm a)) := by
        rw [hwB', hwB', blockIndex_eq_flatten B Q, blockIndex_eq_flatten B Q
          ((innerReversePermutation (B.flatten Q) R).symm a), hya]
      exact innerReverse_lt_of_label_lt B S hBB h4
  · intro c d hcd hlt
    have hs : ∀ e, (innerReversePermutation B S *
        (w * (innerReversePermutation (B.flatten Q) R)⁻¹)).symm e =
          innerReversePermutation (B.flatten Q) R
            (w.symm ((innerReversePermutation B S).symm e)) := fun e => by
      rw [Equiv.symm_apply_eq]
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply]
    rw [hs, hs]
    have h1 := hxmin.2 c d hcd hlt
    have h1' := (blockIndex_eq_iff_of_conjugatesLevi hx
      ((innerReversePermutation B S).symm c) ((innerReversePermutation B S).symm d)).mp
      (by simpa only [Equiv.apply_symm_apply] using hcd)
    have h2 := hmin.2 _ _ h1' h1
    have h2' := (blockIndex_eq_iff_of_conjugatesLevi hw
      (w.symm ((innerReversePermutation B S).symm c))
      (w.symm ((innerReversePermutation B S).symm d))).mp
      (by simpa only [Equiv.apply_symm_apply] using h1')
    exact hymin.1 _ _ h2' h2

end Labels

section Localize

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (Q S : BlockRefinement B)
  {V : Type uV} {X : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

/-- A whole-target upper piece of the product-Levi geometric lemma, read in the
inner-reversed target coordinates, localizes to a transported inner opposite
Jacquet module of the source along the original target. -/
theorem localization_of_upperPiece
    (σ : Representation ℂ ((B.flatten Q).Levi F.Carrier) V)
    (Sf : BlockRefinement (B.flatten Q)) {w : Equiv.Perm (Fin n)} (hwB : w ∈ blockWeyl B)
    (hmin : IsMinimalRepresentative (B.flatten Q) (B.flatten (reverseRefinement B S)) w)
    (hw : ConjugatesLevi (F := F.Carrier) ((B.flatten Q).flatten Sf)
      (B.flatten (reverseRefinement B S)) w)
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) X)
    (h : IsSubquotient
      (transport ((B.flatten Q).flatten Sf) (B.flatten (reverseRefinement B S)) w hw
        ((T.normalizedRefinedJacquet (B.flatten Q) Sf σ).comp
          (flattenedLeviEquiv F.Carrier (B.flatten Q) Sf).toMonoidHom))
      (ρ.comp (leviConjugation (B.flatten (reverseRefinement B S)) (B.flatten S)
        (innerReversePermutation B S)
        (conjugatesLevi_innerReverse B S F.Carrier)).toMonoidHom)) :
    ∃ g ∈ blockWeyl B, ∃ (R' : BlockRefinement (B.flatten Q))
      (hg : ConjugatesLevi (F := F.Carrier) ((B.flatten Q).flatten R') (B.flatten S) g),
      IsMinimalRepresentative (B.flatten Q) (B.flatten S) g ∧
      IsSubquotient
        (transport ((B.flatten Q).flatten R') (B.flatten S) g hg
          ((T.normalizedRefinedOppositeJacquet (B.flatten Q) R' σ).comp
            (flattenedLeviEquiv F.Carrier (B.flatten Q) R').toMonoidHom))
        ρ := by
  obtain ⟨R', rfl⟩ : ∃ R', reverseRefinement (B.flatten Q) R' = Sf :=
    ⟨reverseRefinement (B.flatten Q) Sf, reverseRefinement_reverseRefinement _ Sf⟩
  have hx := conjugatesLevi_innerReverse B S F.Carrier
  have hy := conjugatesLevi_innerReverse (B.flatten Q) R' F.Carrier
  have hyw := conjugatesLevi_mul (conjugatesLevi_inv hy) hw
  have hg := conjugatesLevi_mul hyw hx
  have hgB : innerReversePermutation B S *
      (w * (innerReversePermutation (B.flatten Q) R')⁻¹) ∈ blockWeyl B :=
    mul_mem (blockPermOf_mem_blockWeyl B _) (mul_mem hwB
      (inv_mem (blockWeyl_flatten_le B Q (blockPermOf_mem_blockWeyl _ _))))
  refine ⟨_, hgB, R', hg,
    isMinimalRepresentative_localized F.Carrier Q S R' hwB hmin hw, ?_⟩
  let U := (T.normalizedRefinedJacquet (B.flatten Q)
      (reverseRefinement (B.flatten Q) R') σ).comp
    (flattenedLeviEquiv F.Carrier (B.flatten Q) (reverseRefinement (B.flatten Q) R')).toMonoidHom
  have e := flattenedNormalizedOppositeReverseEquiv (B.flatten Q) R' T σ
  rw [transport_mul hyw hx, transport_mul (conjugatesLevi_inv hy) hw]
  have hU : transport _ _ (innerReversePermutation (B.flatten Q) R')⁻¹
      (conjugatesLevi_inv hy)
      (transport _ _ (innerReversePermutation (B.flatten Q) R') hy U) = U := by
    rw [transport_inv hy]
    refine MonoidHom.ext fun m => ?_
    simp only [transport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
  have h' := h.comp (leviConjugation (B.flatten (reverseRefinement B S)) (B.flatten S)
    (innerReversePermutation B S) hx).symm.toMonoidHom
  have hρ : (ρ.comp (leviConjugation (B.flatten (reverseRefinement B S)) (B.flatten S)
      (innerReversePermutation B S) hx).toMonoidHom).comp
      (leviConjugation (B.flatten (reverseRefinement B S)) (B.flatten S)
        (innerReversePermutation B S) hx).symm.toMonoidHom = ρ := by
    refine MonoidHom.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [hρ] at h'
  have h'' : IsSubquotient
      (transport _ _ (innerReversePermutation B S) hx
        (transport _ _ w hw
          (transport _ _ (innerReversePermutation (B.flatten Q) R')⁻¹ (conjugatesLevi_inv hy)
            (transport _ _ (innerReversePermutation (B.flatten Q) R') hy U)))) ρ := by
    rw [hU]
    exact h'
  exact IsSubquotient.of_equiv_left
    (CuspidalSupport.transportEquiv _ hx (CuspidalSupport.transportEquiv _ hw
      (CuspidalSupport.transportEquiv _ (conjugatesLevi_inv hy) e.symm))) h''

end Localize

/-- The product-Levi geometric lemma implies the product-Levi cuspidal
localization statement. -/
theorem productLeviCuspidalLocalization_of_geometricLemma
    (hgeo : PadicProductLeviGeometricLemmaTheorem.{uF, uM}) :
    GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM} := by
  intro p _ F T n hn B Q D σ hσ S' ρ hirr hcusp hsub
  let := T.topology
  obtain ⟨Sf, Rf, hS, hR, m, e, hglue⟩ := hgeo p F T n hn B Q (reverseRefinement B S')
  let σs : SmoothRep.{0, uF, uM} ℂ ((B.flatten Q).Levi F.Carrier) := ⟨σ, hσ⟩
  have hx := conjugatesLevi_innerReverse B S' F.Carrier
  let lc := leviConjugation (B.flatten (reverseRefinement B S')) (B.flatten S')
    (innerReversePermutation B S') hx
  let ρ' := ρ.ρ.comp lc.toMonoidHom
  have : Representation.IsIrreducible ρ' :=
    isIrreducible_comp_of_surjective ρ.ρ lc.toMonoidHom lc.surjective
  have hxmin := isMinimalRepresentative_innerReverse B S'
  have hxinv : IsMinimalRepresentative (B.flatten S') (B.flatten (reverseRefinement B S'))
      (innerReversePermutation B S')⁻¹ := by
    constructor
    · exact hxmin.2
    · simpa only [Equiv.Perm.inv_def, Equiv.symm_symm] using hxmin.1
  have hρ' : IsLeviQuasicuspidal (B.flatten (reverseRefinement B S')) ρ' := by
    have h := isLeviQuasicuspidal_transport (B.flatten S') (B.flatten (reverseRefinement B S'))
      _ hxinv (conjugatesLevi_inv hx) ρ.ρ hcusp.2
    rwa [transport_inv hx] at h
  have h₁ : IsSubquotient ((innerJacquetInductionFunctor.{uF, uM} T B Q
      (reverseRefinement B S')).obj σs).ρ ρ' := by
    have h0 := (IsSubquotient.of_equiv_left
      (flattenedNormalizedOppositeReverseEquiv B S' T (middleInduced T B Q σ).ρ) hsub).comp
        lc.toMonoidHom
    have hJ : (transport (B.flatten (reverseRefinement B S')) (B.flatten S')
        (innerReversePermutation B S') hx
        ((T.normalizedRefinedJacquet B (reverseRefinement B S')
          (middleInduced T B Q σ).ρ).comp
          (flattenedLeviEquiv F.Carrier B (reverseRefinement B S')).toMonoidHom)).comp
          lc.toMonoidHom =
        (T.normalizedRefinedJacquet B (reverseRefinement B S')
          (middleInduced T B Q σ).ρ).comp
          (flattenedLeviEquiv F.Carrier B (reverseRefinement B S')).toMonoidHom := by
      refine MonoidHom.ext fun g => ?_
      simp only [transport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, lc]
    rw [hJ] at h0
    exact h0
  obtain ⟨i, hi⟩ := IsGluedFrom.exists_isSubquotient_piece hglue σs h₁
  have hSi := hS (e i)
  have hRi := hR (e i)
  by_cases hpar : refinedParabolic F.Carrier (B.flatten (reverseRefinement B S')) (Rf (e i)) = ⊤
  swap
  · have hi' : IsSubquotient
        ((T.normalizedRefinedInductionFunctor (B.flatten (reverseRefinement B S'))
          (Rf (e i))).obj _).representation ρ' := hi
    exact absurd hi' (GeometricExcessBranch.not_isSubquotient_properInduced T hn _
      (Rf (e i)) hpar _ ρ' inferInstance hρ')
  have htop : sourceLevi F.Carrier (B.flatten (reverseRefinement B S')) (B.flatten Q)
      (e i).val.val⁻¹ = ⊤ :=
    hRi.2.1.trans (refinedLevi_eq_top_of_refinedParabolic_eq_top _ (Rf (e i)) hpar)
  have hw := InducedOppositeCuspidalPiece.conjugatesLevi_flatten_of_intersections (B.flatten Q)
    (B.flatten (reverseRefinement B S')) (Sf (e i)) (e i).val.val hSi.2.1 htop
  have h₂ := IsSubquotient.of_equiv_left
    (wholeLeviGeometricPieceEquiv T (B.flatten Q) (B.flatten (reverseRefinement B S'))
      (e i).val.val (Sf (e i)) (Rf (e i)) hSi.2.1 hRi.2.1 hw σs).symm hi
  exact localization_of_upperPiece T B Q S' σ.ρ (Sf (e i)) (e i).property
    (e i).val.property hw ρ.ρ h₂

end Langlands.ProductLeviCuspidalLocalization
