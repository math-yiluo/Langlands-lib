import Langlands.GroupScheme.Rational.NormalizerWeightSupport
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite sums of actual normalized-subgroup tangent weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The full tangent-weight support of any subgroup functor is finite for
conjugation by a split torus, including zero when it occurs. -/
theorem IsSplitTorus.finite_actionWeightSupport (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) :
    (RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation i) F).Finite := by
  apply (hT.finite_weightSupport i).subset
  rintro χ ⟨X, hX0, hXχ, _⟩ hzero
  rw [RelativeRoot.actionWeightSpace_conjugation, hzero, Submodule.mem_bot] at hXχ
  exact hX0 hXχ

namespace RelativeRoot

/-- A finite enumeration of the actual full tangent-weight support. -/
@[instance_reducible]
def actionWeightSupportFintypeOfIsSplitTorus (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) :
    Fintype (actionWeightSupport (AutomorphicAction.conjugation i) F) :=
  (hT.finite_actionWeightSupport i F).fintype

/-- The integral sum of the distinct characters occurring in the actual
tangent support of the subgroup. Each occurring character is counted once. -/
def actionWeightSum (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) : characterLattice T :=
  letI := actionWeightSupportFintypeOfIsSplitTorus hT i F
  ∑ χ : actionWeightSupport (AutomorphicAction.conjugation i) F, χ.val

/-- Pairing the actual support sum is the sum of the integral pairings. -/
theorem latticePairing_actionWeightSum (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) (ν : cocharacterLattice T) :
    latticePairing T (actionWeightSum hT i F) ν =
      letI := actionWeightSupportFintypeOfIsSplitTorus hT i F
      ∑ χ : actionWeightSupport (AutomorphicAction.conjugation i) F,
        latticePairing T χ.val ν := by
  classical
  let := actionWeightSupportFintypeOfIsSplitTorus hT i F
  exact map_sum ((latticePairing T).flip ν) _ _

/-- A nonempty support of strictly positive weights has strictly positive
integral pairing with its support sum. -/
theorem latticePairing_actionWeightSum_pos (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) (ν : cocharacterLattice T)
    (hne : (actionWeightSupport (AutomorphicAction.conjugation i) F).Nonempty)
    (hpos : ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) F,
      0 < latticePairing T χ ν) :
    0 < latticePairing T (actionWeightSum hT i F) ν := by
  classical
  let := actionWeightSupportFintypeOfIsSplitTorus hT i F
  rw [latticePairing_actionWeightSum]
  apply Finset.sum_pos
  · intro χ _
    exact hpos χ.val χ.property
  · obtain ⟨χ, hχ⟩ := hne
    exact ⟨⟨χ, hχ⟩, Finset.mem_univ _⟩

/-- In particular, a nonempty positive support has nonzero support sum. -/
theorem actionWeightSum_ne_zero_of_pos (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) (ν : cocharacterLattice T)
    (hne : (actionWeightSupport (AutomorphicAction.conjugation i) F).Nonempty)
    (hpos : ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) F,
      0 < latticePairing T χ ν) :
    actionWeightSum hT i F ≠ 0 := by
  intro hzero
  have h := latticePairing_actionWeightSum_pos hT i F ν hne hpos
  simp only [hzero, map_zero, LinearMap.zero_apply, lt_self_iff_false] at h

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (t : T.toGrp ⟶ H) [Mono t.hom.hom.left]

/-- The actual rational normalizer quotient fixes the sum of all weights
of any subgroup normalized on every test. No finite quotient is required. -/
theorem relativeWeylCharacterAction_actionWeightSum
    (hT : IsSplitTorus T.toGrp) (F : SubgroupFunctor G)
    (hF : (AutomorphicAction.conjugation j).IsStable F) (w : relativeWeylGroup t) :
    relativeWeylCharacterAction t w (actionWeightSum hT (t ≫ j) F) =
      actionWeightSum hT (t ≫ j) F := by
  classical
  let := actionWeightSupportFintypeOfIsSplitTorus hT (t ≫ j) F
  change relativeWeylCharacterAction t w
    (∑ χ : actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F, χ.val) =
      ∑ χ : actionWeightSupport (AutomorphicAction.conjugation (t ≫ j)) F, χ.val
  rw [map_sum]
  exact Fintype.sum_equiv (normalizedWeightPermutation j t hF w) _ _ (fun _ => rfl)

end RelativeRoot

end Langlands.GroupScheme
