import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.RootSubgroupSeparation

/-! # Actual root points outside opposite dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T}

include hT

/-- The first root weight belongs to the actual tangent submodule of its
intrinsic root functor. -/
theorem weightSpace_le_tangentSubmodule_subgroup (ha : a ≠ 0) :
    weightSpace i a ≤ tangentSubmodule (subgroup i a) := by
  rw [tangentSubmodule_subgroup i a hT ha]
  have ha1 : a ∈ cyclicTail a 1 := ⟨1, le_rfl, by decide, by simp⟩
  simpa only [semigroupWeightSpan, actionWeightSpace_conjugation] using
    (le_iSup (fun χ : cyclicTail a 1 =>
      actionWeightSpace (AutomorphicAction.conjugation i) χ.val) ⟨a, ha1⟩)

/-- An actual nonidentity infinitesimal root point outside the opposite
dynamic parabolic, over the original field's dual numbers. -/
def rootPointOutsideNegativeParabolic (ha : a ∈ relativeRoots i)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν) :
    {g : (algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))) ⟶ G.X //
      g ∈ (subgroup i a).carrier _ ∧ g ≠ 1 ∧
        g ∉ (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)).carrier _} := by
  let hex := (weightSpace i a).ne_bot_iff.mp ha.2
  let X := Classical.choose hex
  have hX : X ∈ weightSpace i a := (Classical.choose_spec hex).1
  have hX0 : X ≠ 0 := (Classical.choose_spec hex).2
  have hXroot : X.toMul.val ∈ (subgroup i a).carrier _ :=
    weightSpace_le_tangentSubmodule_subgroup i hT ha.1 hX
  have hX1 : X.toMul.val ≠ 1 := by
    intro h
    apply hX0
    apply Additive.toMul.injective
    exact Subtype.ext h
  refine ⟨X.toMul.val, hXroot, hX1, ?_⟩
  intro hXP
  exact hX1 (eq_one_of_mem_subgroup_of_mem_negative_parabolic i ν hpos hXroot hXP)

/-- A cocharacter negative on an actual root defines a proper all-test
dynamic parabolic. No rational root-point existence is required. -/
theorem negativeParabolic_ne_top (ha : a ∈ relativeRoots i)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν) :
    Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i) ≠ ⊤ := by
  intro h
  obtain ⟨g, _, _, hg⟩ := rootPointOutsideNegativeParabolic i hT ha ν hpos
  apply hg
  rw [h]
  exact Subgroup.mem_top g

end Langlands.GroupScheme.RelativeRoot
