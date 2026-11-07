import Langlands.Representation.Exponents.FullParabolicExponentCone
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction

/-! # A restricted root witnessing properness of an actual parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a) (hG : IsConnectedReductive G)

include hG

/-- Empty complementary restricted roots force the original parabolic map
to be an isomorphism, on all test schemes. -/
theorem isIso_of_restrictedRoots_eq_empty
    (h : r.restrictedRoots = ∅) : IsIso p := by
  have hJ : r.data.J = simpleRelativeRoots r.data.i r.data.ν :=
    Set.Subset.antisymm r.isCompatible.subset_simpleRoots
      (r.restrictedRoots_eq_empty_iff.mp h)
  have htop : SubgroupFunctor.range p = ⊤ := by
    rw [r.isCompatible.parabolic_eq, hJ]
    exact standardParabolic_simple_eq_top_of_relativeRootNegation relativeRootNegation
      k G hG r.data.T r.data.i r.isCompatible.maximalSplit r.data.ν
      r.isCompatible.generic
  let : IsClosedImmersion p.hom.hom.left := r.isCompatible.parabolic.isClosedSubgroup
  exact isIso_of_full_range p (Over.mono_of_mono_left _) htop

/-- A proper actual parabolic has a nonempty restricted-root set in every
compatible presentation. -/
theorem restrictedRoots_nonempty_of_not_isIso (hproper : ¬ IsIso p) :
    r.restrictedRoots.Nonempty :=
  Set.nonempty_iff_ne_empty.mpr
    (fun h => hproper (r.isIso_of_restrictedRoots_eq_empty hG h))

/-- An actual restricted simple root selected from a supplied compatible
presentation of a proper parabolic. -/
def properRestrictedRoot (hproper : ¬ IsIso p) : r.restrictedRoots :=
  ⟨(r.restrictedRoots_nonempty_of_not_isIso hG hproper).choose,
    (r.restrictedRoots_nonempty_of_not_isIso hG hproper).choose_spec⟩

/-- The selected root has strictly positive defining-component evaluation. -/
theorem properRestrictedRoot_evaluation_pos (hproper : ¬ IsIso p) :
    0 < r.splitComponentEvaluation (r.properRestrictedRoot hG hproper) :=
  r.splitComponentEvaluation_pos_of_mem_restrictedRoots
    (r.properRestrictedRoot hG hproper).property

variable [LocallyOfFiniteType G.X.hom]

/-- The restricted-root set of a compatible presentation is empty precisely
when the original actual parabolic is full. -/
theorem restrictedRoots_eq_empty_iff_isIso :
    r.restrictedRoots = ∅ ↔ IsIso p := by
  constructor
  · exact r.isIso_of_restrictedRoots_eq_empty hG
  · intro hp
    let := hp
    let := r.isCompatible.levi.isIso_of_isIso_parabolic (p := p) hG
    exact r.restrictedRoots_eq_empty_iff.mpr
      (r.simpleRelativeRoots_subset_of_range_eq_top
        (SubgroupFunctor.range_eq_top_of_isIso (l ≫ p)))

/-- Zero is excluded from the strict cone of every compatible presentation
of a proper actual parabolic. -/
theorem zero_notMem_positiveCone_of_not_isIso (hproper : ¬ IsIso p) :
    (0 : RealTorusSpace.Vstar A) ∉ r.positiveCone := by
  intro hzero
  exact hproper (r.isIso_of_restrictedRoots_eq_empty hG
    (r.zero_mem_positiveCone_iff_restrictedRoots_eq_empty.mp hzero))

end Langlands.GroupScheme.ParabolicRootPresentation
