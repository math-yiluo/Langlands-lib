import Langlands.GroupScheme.IntegralModel.QuotientLifting
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.Geometry.Building.RootDatumValuation

/-! # Zero root values from supplied smooth integral root models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G U : GroupScheme (Spec (CommRingCat.of K))}
  (i : S.toGrp ⟶ G) (a : characterLattice S) (j : U ⟶ G)
  (M : IntegralModel R K U) (φ : RootFunctionFamily S G)
  {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  (q : M.specialFibre ⟶ Q)

/-- Integral root-model sections have nonnegative value, and a positive value
forces trivial image in the specified special-fibre quotient. -/
def RootModelReductionCompatible : Prop :=
  (∀ x : M.integralSections,
    (0 : WithTop ℝ) ≤ φ a (rationalPoints.map j (M.integralPointMap x))) ∧
  (∀ x : M.integralSections,
    (0 : WithTop ℝ) < φ a (rationalPoints.map j (M.integralPointMap x)) →
      rationalPoints.map q (M.reduction x) = 1)

variable {i a j M φ q}

/-- A residue section with nontrivial quotient image lifts to a generic
root-group point of value exactly zero. -/
theorem exists_zero_rootPoint_of_nontrivial_reduction
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
    (hM : M.IsSmooth) (hc : RootModelReductionCompatible a j M φ q)
    (y : rationalPoints M.specialFibre) (hy : rationalPoints.map q y ≠ 1) :
    ∃ g : rationalPoints G, g ∈ rootGroupPoints i a ∧ φ a g = (0 : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := M.reduction_surjective hM y
  refine ⟨rationalPoints.map j (M.integralPointMap x), ?_, ?_⟩
  · change rationalPoints.map j (M.integralPointMap x) ∈
      (RelativeRoot.subgroup i a).carrier _
    rw [← hj.2]
    exact ⟨M.integralPointMap x, rfl⟩
  · apply le_antisymm _ (hc.1 x)
    apply le_of_not_gt
    intro hpos
    apply hy
    rw [← hx]
    exact hc.2 x hpos

variable
  {N : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  [Smooth N.X.hom] [IsAffineHom Q.X.hom]
  {L : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  [IsAffineHom L.X.hom] [Smooth L.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}

/-- A quotient representing an actual root subgroup of a smooth affine
residue group has a nontrivial point, which lifts through reduction. -/
theorem exists_zero_rootPoint_of_quotient_root
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
    (hM : M.IsSmooth) (hc : RootModelReductionCompatible a j M φ q)
    (n : N ⟶ M.specialFibre) (hn : IsClosedSubgroup n)
    (hN : RelativeRoot.IsSplitUnipotent N)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hT : IsSplitTorus T.toGrp) (iT : T.toGrp ⟶ L)
    {b : characterLattice T} (hb : b ∈ relativeRoots iT)
    (l : Q ⟶ L) (hl : (RelativeRoot.subgroup iT b).IsRepresentedBy l) :
    ∃ g : rationalPoints G, g ∈ rootGroupPoints i a ∧ φ a g = (0 : WithTop ℝ) := by
  obtain ⟨y, hyroot, hy⟩ := RelativeRoot.exists_rootPoint_actual hT iT hb
  rw [← hl.2] at hyroot
  obtain ⟨z, hz⟩ := hyroot
  have hz1 : z ≠ 1 := by
    intro h
    apply hy
    rw [← hz, h, map_one]
  let x := M.quotientReductionLift hM n hn hN q hq z
  have hx : rationalPoints.map q (M.reduction x) = z :=
    M.quotientReductionLift_spec hM n hn hN q hq z
  exact exists_zero_rootPoint_of_nontrivial_reduction hj hM hc
    (M.reduction x) (by rwa [hx])

/-- A chosen actual generic root point with value zero, for a supplied
smooth root model and a nontrivial residue quotient root. -/
def smoothRootModelZeroPoint
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
    (hM : M.IsSmooth) (hc : RootModelReductionCompatible a j M φ q)
    (n : N ⟶ M.specialFibre) (hn : IsClosedSubgroup n)
    (hN : RelativeRoot.IsSplitUnipotent N)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hT : IsSplitTorus T.toGrp) (iT : T.toGrp ⟶ L)
    {b : characterLattice T} (hb : b ∈ relativeRoots iT)
    (l : Q ⟶ L) (hl : (RelativeRoot.subgroup iT b).IsRepresentedBy l) :
    rationalPoints G :=
  Classical.choose
    (exists_zero_rootPoint_of_quotient_root hj hM hc n hn hN hq hT iT hb l hl)

/-- The chosen point lies in the actual generic root group and has value zero. -/
theorem smoothRootModelZeroPoint_spec
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
    (hM : M.IsSmooth) (hc : RootModelReductionCompatible a j M φ q)
    (n : N ⟶ M.specialFibre) (hn : IsClosedSubgroup n)
    (hN : RelativeRoot.IsSplitUnipotent N)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hT : IsSplitTorus T.toGrp) (iT : T.toGrp ⟶ L)
    {b : characterLattice T} (hb : b ∈ relativeRoots iT)
    (l : Q ⟶ L) (hl : (RelativeRoot.subgroup iT b).IsRepresentedBy l) :
    smoothRootModelZeroPoint hj hM hc n hn hN hq hT iT hb l hl ∈ rootGroupPoints i a ∧
      φ a (smoothRootModelZeroPoint hj hM hc n hn hN hq hT iT hb l hl) =
        (0 : WithTop ℝ) :=
  Classical.choose_spec
    (exists_zero_rootPoint_of_quotient_root hj hM hc n hn hN hq hT iT hb l hl)

end Langlands.Geometry.Building
