import Langlands.Group.RelativeWeylCoatomSurvivors
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy

/-! # When the selected relative Weyl class contributes to the tested Bruhat sum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Aubert.General.RationalPointFamily
  Langlands.Group.RelativeWeylIndexing

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  {CM : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem CM (relativeWeylGroup i))
  [Finite (relativeWeylGroup i)] [Fintype (SimpleRoot i ν)]

local notation "act" => schemeWeylCharacterAction i

omit [Fintype (SimpleRoot i ν)] in
private theorem mapsIntoSimple_of_rootSet_maps
    (hT : IsSplitTorus T.toGrp) (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    {w : relativeWeylGroup i} {A B : Finset (SimpleRoot i ν)}
    (h : ∀ a ∈ rootSet i ν A, act w a ∈ rootSet i ν B) :
    MapsIntoSimple cs w A B := by
  intro a ha
  obtain ⟨b, hb, he⟩ := h a.val ((val_mem_rootSet i ν A a).mpr ha)
  have hpos : act w a.val ∈ positiveRelativeRoots i ν := he ▸ b.property.1
  exact ⟨b, hb, (hcs.conj_simple_iff hT w a b hpos).mpr he.symm⟩

/-- When the selected Weyl class exchanges the two Levi simple-root sets, it is
minimal for tests inside the target. For any test where it is minimal, its target
intersection equals the tested index precisely for such nested tests. Its source
intersection for the full target is the original source. -/
def SelectedBruhatGeometryStatement : Prop :=
  IsSplitTorus T.toGrp → IsRelativeWeylCoxeterRealization i ν cs →
    ∀ (I Q : Finset (SimpleRoot i ν)) (w : relativeWeylGroup i),
      (∀ a ∈ rootSet i ν I, act w a ∈ rootSet i ν Q) →
      (∀ a ∈ rootSet i ν Q, act w⁻¹ a ∈ rootSet i ν I) →
      (∀ J : Finset (SimpleRoot i ν), J ⊆ Q → IsMinimal cs J I w) ∧
      (∀ J : Finset (SimpleRoot i ν), IsMinimal cs J I w →
        (intersectionSubset cs I J w⁻¹ = J ↔ J ⊆ Q)) ∧
      intersectionSubset cs Q I w = I

/-- Positivity proves minimality, and the simple-reflection intersection
criterion detects the full target and full source intersections. -/
theorem selectedBruhatGeometry : SelectedBruhatGeometryStatement i ν cs := by
  intro hT hcs I Q w hw hv
  have hmin (J : Finset (SimpleRoot i ν)) (hJ : J ⊆ Q) : IsMinimal cs J I w := by
    apply ((minimalityLengthCriterion_proof cs) J I w).mpr
    constructor
    · intro a ha
      have hpos := simpleRelativeRoots_subset_positive i ν
        (rootSet_subset i ν I (hv _ ((val_mem_rootSet i ν Q a).mpr (hJ ha))))
      have h := (hcs.2.2.1 w⁻¹ a).mpr hpos
      rw [← cs.length_inv (w⁻¹ * cs.simple a), mul_inv_rev,
        CoxeterSystem.inv_simple, inv_inv, cs.length_inv] at h
      exact h
    · intro a ha
      exact (hcs.2.2.1 w a).mpr (simpleRelativeRoots_subset_positive i ν
        (rootSet_subset i ν Q (hw _ ((val_mem_rootSet i ν I a).mpr ha))))
  refine ⟨hmin, ?_, ?_⟩
  · intro J hJmin
    have hInv := isMinimal_inv cs hJmin
    rw [intersectionSubset_eq_source_iff_mapsIntoSimple cs hInv]
    constructor
    · intro hmap a ha
      obtain ⟨b, hb, he⟩ := hmap a ha
      have hpos := (hcs.2.2.1 w⁻¹ a).mp
        (((minimalityLengthCriterion_proof cs) I J w⁻¹).mp hInv |>.2 a ha)
      have hab := hcs.root_eq_of_conj_simple w⁻¹ a b hpos he
      have hba := congrArg (act w) hab
      rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at hba
      exact (val_mem_rootSet i ν Q a).mp
        (hba.symm ▸ hw _ ((val_mem_rootSet i ν I b).mpr hb))
    · intro hJ
      apply mapsIntoSimple_of_rootSet_maps i ν cs hT hcs
      intro a ha
      exact hv a ((rootSet_subset_iff i ν J Q).mpr hJ ha)
  · exact (intersectionSubset_eq_source_iff_mapsIntoSimple cs (hmin Q (fun _ h => h))).mpr
      (mapsIntoSimple_of_rootSet_maps i ν cs hT hcs hw)

end Langlands.Global
