import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.RootSubgroupStability
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Excluded intrinsic weights of relative root representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G)
    (a : characterLattice S)

section RepresentedMap

variable {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (j : U ⟶ G)
    (hj : (subgroup i a).IsRepresentedBy j)

/-- The actual representing inclusion maps intrinsic root weights to ambient
adjoint weights by its differential. -/
def subgroupActionWeightMap (χ : characterLattice S) :
    actionWeightSpace (subgroupAction i a j hj) χ →ₗ[k] weightSpace i χ where
  toFun X := ⟨Lie.targetMapLinear j k X, by
    rw [← actionWeightSpace_conjugation i χ]
    exact lieKernelTargetLinear_mem_actionWeightSpace
      (AutomorphicAction.conjugation i) (subgroupAction i a j hj) j
      (fun _ s x => AutomorphicAction.onRepresentedSubgroup_act_comp
        (AutomorphicAction.conjugation i) j hj (subgroup_isStable i a) s x)
      χ X.property⟩
  map_add' X Y := Subtype.ext (map_add (Lie.targetMapLinear j k)
    (X : Additive (lieKernel U k)) (Y : Additive (lieKernel U k)))
  map_smul' c X := Subtype.ext (map_smul (Lie.targetMapLinear j k) c
    (X : Additive (lieKernel U k)))

@[simp] theorem subgroupActionWeightMap_coe (χ : characterLattice S)
    (X : actionWeightSpace (subgroupAction i a j hj) χ) :
    (subgroupActionWeightMap i a j hj χ X : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k X := rfl

/-- The canonical map is injective because a representative is a monomorphic
subgroup inclusion. -/
theorem subgroupActionWeightMap_injective (χ : characterLattice S) :
    Function.Injective (subgroupActionWeightMap i a j hj χ) := by
  have : Mono j.hom.hom := hj.1
  intro X Y h
  apply Subtype.ext
  apply Lie.targetMapLinear_injective j k
  exact congrArg (fun Z : weightSpace i χ => (Z : Additive (lieKernel G k))) h

end RepresentedMap

variable [LocallyOfFiniteType G.X.hom] (hS : IsSplitTorus S.toGrp)

include hS

/-- A character outside the positive multiples has weight space disjoint
from the full positive cyclic Lie span. -/
theorem disjoint_weightSpace_positiveWeightSpan
    (χ : characterLattice S)
    (hχ : ∀ n : ℕ, 0 < n → n • a ≠ χ) :
    Disjoint (weightSpace i χ) (positiveWeightSpan i a) := by
  have hind : iSupIndep (weightSpace i) := by
    have heq : actionWeightSpace (AutomorphicAction.conjugation i) = weightSpace i :=
      funext (actionWeightSpace_conjugation i)
    rw [← heq]
    exact iSupIndep_actionWeightSpace (AutomorphicAction.conjugation i) hS
  apply ((iSupIndep_def.mp hind) χ).mono_right
  refine iSup_le fun n => ?_
  exact le_iSup_of_le (n.val • a)
    (le_iSup_of_le (hχ n.val n.property) le_rfl)

/-- Exact positive Lie image excludes every other character from the actual
ambient support of the root functor. -/
theorem notMem_actionWeightSupport_subgroup_of_hasLieImage
    (hLie : HasLieImage (subgroup i a) (positiveWeightSpan i a))
    (χ : characterLattice S)
    (hχ : ∀ n : ℕ, 0 < n → n • a ≠ χ) :
    χ ∉ actionWeightSupport (AutomorphicAction.conjugation i) (subgroup i a) := by
  rintro ⟨X, hX0, hXχ, hXF⟩
  rw [actionWeightSpace_conjugation] at hXχ
  exact hX0 ((Submodule.disjoint_def.mp
    (disjoint_weightSpace_positiveWeightSpan i a hS χ hχ)) X hXχ ((hLie X).mp hXF))

section Represented

variable {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] (j : U ⟶ G)
    (hj : (subgroup i a).IsRepresentedBy j)
    (hLie : HasLieImage (subgroup i a) (positiveWeightSpan i a))

include hLie

/-- The actual induced torus action on every representative has no intrinsic
weight outside the positive multiples of the chosen character. -/
theorem subgroupAction_weightSpace_eq_bot_of_hasLieImage
    (χ : characterLattice S)
    (hχ : ∀ n : ℕ, 0 < n → n • a ≠ χ) :
    actionWeightSpace (subgroupAction i a j hj) χ = ⊥ := by
  exact actionWeightSpace_onRepresentedSubgroup_eq_bot
    (AutomorphicAction.conjugation i) j hj (subgroup_isStable i a) χ
    (notMem_actionWeightSupport_subgroup_of_hasLieImage i a hS hLie χ hχ)

/-- A nonzero split-torus character has no zero intrinsic Lie weight on any
root representative with the full positive Lie image. -/
theorem subgroupAction_zero_weightSpace_eq_bot_of_hasLieImage
    (ha : a ≠ 0) :
    actionWeightSpace (subgroupAction i a j hj) 0 = ⊥ := by
  apply subgroupAction_weightSpace_eq_bot_of_hasLieImage i a hS j hj hLie
  intro n hn
  exact hS.nsmul_ne_zero ha (Nat.ne_of_gt hn)

end Represented

end Langlands.GroupScheme.RelativeRoot
