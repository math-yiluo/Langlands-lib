import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Regular refinements of actual cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A positive multiplier dominating the pairings of the chosen generic
cocharacter with every actual root. -/
def regularRefinementMultiplier (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) : ℕ :=
  IntegralPerturbation.bound
    (fun alpha : characterLattice T => (latticePairing T alpha).toAddMonoidHom)
    (hT.finite_relativeRoots i).toFinset (genericCocharacterOfIsSplitTorus hT i)

/-- An actual regular cocharacter obtained by a bounded generic perturbation
of a positive multiple of the given cocharacter. -/
def regularRefinement (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (nu : cocharacterLattice T) : cocharacterLattice T :=
  regularRefinementMultiplier hT i • nu + genericCocharacterOfIsSplitTorus hT i

theorem regularRefinementMultiplier_pos (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) :
    0 < regularRefinementMultiplier hT i :=
  IntegralPerturbation.bound_pos _ _ _

/-- The root signs of the refinement are lexicographic in the original
cocharacter and then the chosen generic cocharacter. -/
theorem regularRefinement_signs (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (nu : cocharacterLattice T) {alpha : characterLattice T} (halpha : alpha ∈ roots i) :
    (0 < latticePairing T alpha (regularRefinement hT i nu) ↔
      0 < latticePairing T alpha nu ∨
        latticePairing T alpha nu = 0 ∧
          0 < latticePairing T alpha (genericCocharacterOfIsSplitTorus hT i)) ∧
    (latticePairing T alpha (regularRefinement hT i nu) < 0 ↔
      latticePairing T alpha nu < 0 ∨
        latticePairing T alpha nu = 0 ∧
          latticePairing T alpha (genericCocharacterOfIsSplitTorus hT i) < 0) ∧
    (latticePairing T alpha (regularRefinement hT i nu) = 0 ↔
      latticePairing T alpha nu = 0 ∧
        latticePairing T alpha (genericCocharacterOfIsSplitTorus hT i) = 0) := by
  exact IntegralPerturbation.signs
    (fun alpha : characterLattice T => (latticePairing T alpha).toAddMonoidHom)
    (hT.finite_relativeRoots i).toFinset nu (genericCocharacterOfIsSplitTorus hT i)
    le_rfl ((hT.finite_relativeRoots i).mem_toFinset.mpr halpha)

theorem regularRefinement_isRegular (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (nu : cocharacterLattice T) : IsRegularCocharacter i (regularRefinement hT i nu) := by
  intro alpha halpha hzero
  exact genericCocharacterOfIsSplitTorus_spec hT i alpha halpha
    (((regularRefinement_signs hT i nu halpha).2.2.mp hzero).2)

/-- Nonnegative root support of the refinement is contained in the original
nonnegative root support. -/
theorem regularRefinement_nonneg (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (nu : cocharacterLattice T) {alpha : characterLattice T} (halpha : alpha ∈ roots i)
    (h : 0 ≤ latticePairing T alpha (regularRefinement hT i nu)) :
    0 ≤ latticePairing T alpha nu := by
  by_contra hneg
  have hlt := (regularRefinement_signs hT i nu halpha).2.1.mpr
    (Or.inl (lt_of_not_ge hneg))
  exact (not_lt_of_ge h) hlt

/-- Every originally positive root remains positive on the refinement. -/
theorem regularRefinement_pos (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (nu : cocharacterLattice T) {alpha : characterLattice T} (halpha : alpha ∈ roots i)
    (h : 0 < latticePairing T alpha nu) :
    0 < latticePairing T alpha (regularRefinement hT i nu) :=
  (regularRefinement_signs hT i nu halpha).1.mpr (Or.inl h)

end Langlands.GroupScheme
