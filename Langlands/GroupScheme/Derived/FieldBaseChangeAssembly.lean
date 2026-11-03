import Langlands.GroupScheme.Derived.FieldBaseChangeProof
import Langlands.GroupScheme.Derived.BaseChangeElementary

/-! # Field base change for the full derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The full derived subgroup of an affine group over a field commutes with
base change along every affine map. -/
theorem derivedSubgroup_baseChange_eq_of_field {k : Type u} [Field k]
    {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k)) [IsAffineHom b]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    (derivedSubgroup G).baseChange b =
      derivedSubgroup ((GroupScheme.baseChange b).obj G) := by
  apply le_antisymm
  · intro T x hx H i hi hcomm
    have : IsClosedImmersion i.hom.hom.left := hi
    have hrep : (SubgroupFunctor.range i).IsClosedRepresentable :=
      ⟨H, i, ⟨Over.mono_of_mono_left _, rfl⟩, hi⟩
    obtain ⟨D, d, hd, hclosed⟩ :=
      SubgroupFunctor.restrictionCore_isClosedRepresentable b _ hrep
    have hcommD : (SubgroupFunctor.range d).ContainsCommutators := by
      rw [hd.2]
      exact hcomm.restrictionCore b
    have hle : derivedSubgroup G ≤
        SubgroupFunctor.restrictionCore b (SubgroupFunctor.range i) := by
      rw [← hd.2]
      exact derivedSubgroup_le_range d hclosed hcommD
    exact SubgroupFunctor.restrictionCore_baseChange_le b _ T
      (SubgroupFunctor.baseChange_mono b hle T hx)
  · exact derivedSubgroup_baseChange_le b

/-- The published field-base-change proposition, including every exhibiting
closed derived-subgroup inclusion and equality on all test schemes. -/
theorem derivedSubgroupFieldBaseChange :
    DerivedSubgroupFieldBaseChangeStatement.{u} := by
  intro k K _ _ _ G _ _ D d hd
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have heq := derivedSubgroup_baseChange_eq_of_field b G
  exact ⟨hd.baseChange_of_eq b heq, heq⟩

end Langlands.GroupScheme
