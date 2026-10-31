import Langlands.Representation.Geometric.GeometricCoarseCentralReflection
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Geometric.IntersectionChamberCoordinates

/-! Fine tuple coordinates for actual inverse-conjugated coarse scalars. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uR uF uV

variable {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)

variable (R₀ : Type uR) [CommRing R₀] (R : BlockRefinement C)
  (hS : sourceLevi R₀ B C w = refinedLevi R₀ B S)
  (hR : sourceLevi R₀ C B w⁻¹ = refinedLevi R₀ C R)

/-- The actual inverse homomorphism is an equivalence of the refined Levis. -/
def inverseRefinedIntersectionEquiv :
    refinedLevi R₀ C R ≃* refinedLevi R₀ B S :=
  (MulEquiv.subgroupCongr hR).symm.trans
    ((intersectionLeviConjugation R₀ B C w).symm.trans
      (MulEquiv.subgroupCongr hS.symm).symm)

@[simp]
theorem inverseRefinedIntersectionEquiv_apply (m : refinedLevi R₀ C R) :
    inverseRefinedIntersectionEquiv B C w S R₀ R hS hR m =
      inverseRefinedIntersectionHom R₀ B C w S R hS hR m := rfl

/-- The inverse-conjugated target coarse scalar is central in the source
refined Levi, without assuming whole-Levi conjugacy. -/
theorem inverseCoarseScalarIntersectionHom_mem_center
    (a : Fin C.length → R₀ˣ) :
    inverseCoarseScalarIntersectionHom R₀ B C w S R hS hR a ∈
      Subgroup.center (refinedLevi R₀ B S) := by
  have hc : coarseScalarRefinedLevi C R R₀ a ∈
      Subgroup.center (refinedLevi R₀ C R) := by
    apply Subgroup.mem_center_iff.mpr
    intro m
    apply Subtype.ext
    change m.val * (coarseScalarRefinedLevi C R R₀ a).val =
      (coarseScalarRefinedLevi C R R₀ a).val * m.val
    rw [coarseScalarRefinedLevi_val]
    exact (C.blockScalarLevi_commute R₀ a m.val).symm
  let e := inverseRefinedIntersectionEquiv B C w S R₀ R hS hR
  exact Subgroup.map_center_le_center e.surjective
    ⟨coarseScalarRefinedLevi C R R₀ a, hc, rfl⟩

private theorem blockScalar_diagonal (D : BlockShape n)
    (a : Fin D.length → R₀ˣ) (x : Fin n) :
    D.blockScalar R₀ a x x = (a (blockIndex D x) : R₀) := by
  rw [D.coe_blockScalar]
  simp only [Matrix.diagonal_apply_eq, blockIndex]

private theorem inversePermutation_conjugate_entry
    (g : GeneralLinear n R₀) (x y : Fin n) :
    ((permutation n R₀ w)⁻¹ * g * permutation n R₀ w) x y = g (w x) (w y) := by
  simpa only [permutation_inv, inv_inv, Equiv.Perm.inv_def, Equiv.symm_symm] using
    permutation_conjugate_entry n R₀ w⁻¹ g x y

/-- Actual inverse conjugation is the explicit pullback of coarse scalar tuples
on every flattened source block. -/
theorem inverseCoarseScalarIntersectionHom_eq_fineScalars
    (a : Fin C.length → R₀ˣ) :
    inverseCoarseScalarIntersectionHom R₀ B C w S R hS hR a =
      flattenedLeviEquiv R₀ B S
        ((B.flatten S).blockScalarLevi R₀
          (chamberRestriction B C w S R₀ a)) := by
  let m := inverseCoarseScalarIntersectionHom R₀ B C w S R hS hR a
  let e := flattenedLeviEquiv R₀ B S
  have hm : m ∈ Subgroup.center (refinedLevi R₀ B S) :=
    inverseCoarseScalarIntersectionHom_mem_center B C w S R₀ R hS hR a
  have hl : e.symm m ∈ Subgroup.center ((B.flatten S).Levi R₀) :=
    Subgroup.map_center_le_center e.symm.surjective ⟨m, hm, rfl⟩
  obtain ⟨b, hb⟩ := (B.flatten S).blockScalarToCenter_bijective R₀ |>.2 ⟨e.symm m, hl⟩
  have hb' : (B.flatten S).blockScalarLevi R₀ b = e.symm m :=
    congrArg Subtype.val hb
  have hmb : m = e ((B.flatten S).blockScalarLevi R₀ b) := by
    rw [hb', e.apply_symm_apply]
  have hmatrix := inverseCoarseScalarIntersectionHom_embedding
    R₀ B C w S R hS hR a
  change B.leviEmbedding R₀ m.val = _ at hmatrix
  rw [hmb, flattenedLeviEquiv_embedding] at hmatrix
  change (B.flatten S).blockScalar R₀ b = _ at hmatrix
  have hbcoord : b = chamberRestriction B C w S R₀ a := by
    funext k
    apply Units.ext
    let x := (B.flatten S).index k ⟨0, (B.flatten S).positive k⟩
    have hx := congrArg (fun g : GeneralLinear n R₀ => g x x) hmatrix
    rw [inversePermutation_conjugate_entry (R₀ := R₀) w,
      blockScalar_diagonal (R₀ := R₀) C] at hx
    change (B.flatten S).blockScalar R₀ b
      ((B.flatten S).index k ⟨0, (B.flatten S).positive k⟩)
      ((B.flatten S).index k ⟨0, (B.flatten S).positive k⟩) = _ at hx
    simp only [(B.flatten S).blockScalar_apply_same, ↓reduceIte] at hx
    exact hx
  rw [hbcoord] at hmb
  exact hmb

/-- The scalar formula as an equality of the actual restriction homomorphisms. -/
theorem inverseCoarseScalarIntersectionHom_eq_fineScalarHom :
    inverseCoarseScalarIntersectionHom R₀ B C w S R hS hR =
      ((flattenedLeviEquiv R₀ B S).toMonoidHom.comp
        ((B.flatten S).blockScalarLevi R₀)).comp
          (chamberRestriction B C w S R₀) := by
  apply MonoidHom.ext
  intro a
  exact inverseCoarseScalarIntersectionHom_eq_fineScalars
    B C w S R₀ R hS hR a

/-- Coarse character reflection in explicit source fine-scalar coordinates.
This remains a restriction along the pulled tuple homomorphism. -/
theorem geometricPiece_coarse_character_reflects_fineScalars
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (hSF : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hRF : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
    IsGeneralizedEigencharacter
      ((((geometricPieceFunctor T B C w S R hSF hRF).obj A).ρ).comp
        (C.blockScalarLevi F.Carrier)) χ →
    IsGeneralizedEigencharacter
      (((T.normalizedRefinedJacquet B S A.representation).comp
        ((flattenedLeviEquiv F.Carrier B S).toMonoidHom.comp
          ((B.flatten S).blockScalarLevi F.Carrier))).comp
            (chamberRestriction B C w S F.Carrier)) χ := by
  let := T.topology
  intro A χ hχ
  have href := geometricPiece_coarse_character_reflects
    T B C w S R hSF hRF A χ hχ
  rw [inverseCoarseScalarIntersectionHom_eq_fineScalarHom] at href
  exact href

end Langlands.Geometric
