import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Rational.RootSubgroupCentralizerAction
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.SemigroupRealizationGeometry

/-! # Intrinsic root functors under restriction between split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

section OverBase

variable {B : Scheme.{u}} {S T : CommGroupScheme B} {G : GroupScheme B}

/-- All larger-torus characters whose restrictions belong to the given semigroup. -/
def characterSemigroupPreimage (f : S ⟶ T)
    (A : AddSubsemigroup (characterLattice S)) :
    AddSubsemigroup (characterLattice T) :=
  A.comap (characterLattice.comapHom (CommGroupScheme.groupHom f))

@[simp] theorem mem_characterSemigroupPreimage (f : S ⟶ T)
    (A : AddSubsemigroup (characterLattice S)) (χ : characterLattice T) :
    χ ∈ characterSemigroupPreimage f A ↔ f ≫ χ ∈ A := Iff.rfl

/-- Conjugation by the larger commutative group preserves every root functor
for the restricted action, on all scheme tests. -/
theorem subgroup_comp_torusHom_isStable (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (a : characterLattice S) :
    (AutomorphicAction.conjugation j).IsStable
      (subgroup (CommGroupScheme.groupHom f ≫ j) a) := by
  apply subgroup_isStable_of_fixes_torus
  intro U t s
  have key : (t * (s ≫ (CommGroupScheme.groupHom f).hom.hom) * t⁻¹) ≫
      j.hom.hom = (s ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ j.hom.hom := by
    rw [mul_inv_cancel_comm]
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at key
  simpa only [AutomorphicAction.conjugation_act, Category.assoc,
    Grp.comp_hom_hom] using key

end OverBase

section Field

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Restricting an actual split-torus action groups the larger weight spaces
by their restricted characters, for every character semigroup. -/
theorem semigroupWeightSpan_comp_torusHom
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (A : AddSubsemigroup (characterLattice S)) :
    semigroupWeightSpan (AutomorphicAction.conjugation
        (CommGroupScheme.groupHom f ≫ j)) A =
      semigroupWeightSpan (AutomorphicAction.conjugation j)
        (characterSemigroupPreimage f A) := by
  simp only [semigroupWeightSpan, actionWeightSpace_conjugation]
  apply le_antisymm
  · refine iSup_le fun ψ => ?_
    rw [weightSpace_comp_eq_iSup hT hS f j ψ.val]
    refine iSup_le fun χ => ?_
    exact le_iSup (fun ξ : characterSemigroupPreimage f A => weightSpace j ξ.val) ⟨χ.val, by
      change f ≫ χ.val ∈ A
      rw [χ.property]
      exact ψ.property⟩
  · refine iSup_le fun χ => ?_
    exact (weightSpace_le_comp f j χ.val).trans
      (le_iSup (fun ψ : A => weightSpace (CommGroupScheme.groupHom f ≫ j) ψ.val)
        ⟨f ≫ χ.val, χ.property⟩)

/-- The intrinsic restricted root functor equals the larger-torus semigroup
subgroup selected by all characters restricting to positive multiples of `a`. -/
theorem subgroup_comp_torusHom_eq_semigroupSubgroup
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0) :
    subgroup (CommGroupScheme.groupHom f ≫ j) a =
      semigroupSubgroup (AutomorphicAction.conjugation j)
        (characterSemigroupPreimage f (cyclicTail a 1)) := by
  apply eq_semigroupSubgroup_of_exact_lieImage
    (AutomorphicAction.conjugation j) hT
    (characterSemigroupPreimage f (cyclicTail a 1))
    (subgroup_isSmoothConnectedClosed_of_ne_zero hS _ a ha)
    (subgroup_comp_torusHom_isStable f j a)
  apply (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
  exact (tangentSubmodule_subgroup _ a hS ha).trans
    (semigroupWeightSpan_comp_torusHom hS hT f j (cyclicTail a 1))

end Field

end Langlands.GroupScheme.RelativeRoot
