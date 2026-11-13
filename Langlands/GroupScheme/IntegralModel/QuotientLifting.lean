import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Integral lifts through split-unipotent special-fibre quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) (hM : M.IsSmooth)
  {N Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  [Smooth N.X.hom] [IsAffineHom Q.X.hom]
  (n : N ⟶ M.specialFibre) (hn : IsClosedSubgroup n)
  (hN : RelativeRoot.IsSplitUnipotent N)
  (q : M.specialFibre ⟶ Q)
  (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)

include hM hn hN hq in
/-- Henselian reduction followed by an actual split-unipotent quotient is
surjective on rational points over the original residue field. -/
theorem quotientReduction_surjective :
    Function.Surjective ((rationalPoints.map q).comp M.reduction) := by
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom
      (CategoryTheory.Limits.pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  obtain ⟨s, hs⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors
    M.specialFibre N n splitUnipotentAffineTorsorStatement
      hn hN Q q hq
  intro y
  obtain ⟨x, hx⟩ := M.reduction_surjective hM (y ≫ s)
  refine ⟨x, ?_⟩
  change M.reduction x ≫ q.hom.hom = y
  rw [hx, Category.assoc, hs, Category.comp_id]

/-- An actual integral section lifting the given residue-quotient point. -/
def quotientReductionLift (y : rationalPoints Q) : M.integralSections :=
  Classical.choose (M.quotientReduction_surjective hM n hn hN q hq y)

/-- The integral lift has the prescribed image in the residue quotient. -/
theorem quotientReductionLift_spec (y : rationalPoints Q) :
    rationalPoints.map q
      (M.reduction (M.quotientReductionLift hM n hn hN q hq y)) = y :=
  Classical.choose_spec (M.quotientReduction_surjective hM n hn hN q hq y)

end Langlands.GroupScheme.IntegralModel
