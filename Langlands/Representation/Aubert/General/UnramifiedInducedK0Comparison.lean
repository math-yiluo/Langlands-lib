import Langlands.Representation.Aubert.General.UnramifiedInducedTrace
import Langlands.Representation.Character.ExactK0Character

/-! # Untwisting a dense normalized induced character comparison in exact K0 -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Aubert.General

open HarmonicAnalysis MeasureTheory Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- The trivial unramified twist is removed by applying the actual normalized
induction functor to the actual trivial-twist isomorphism. -/
def normalizedUnramifiedInductionTrivialTwistIso
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    (normalizedInductionFunctor h hU).obj
        (A.twist (1 : unramifiedCharacters ν).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker ν 1)) ≅
      (normalizedInductionFunctor h hU).obj A :=
  (normalizedInductionFunctor h hU).mapIso
    (SmoothRep.twistOneIso (unramifiedCharacter_isOpen_ker ν 1) A)

section Distribution

variable [MeasurableSpace G] [BorelSpace G] [T2Space G]
  (hproj : Continuous h.projection)
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG] [Measure.IsMulLeftInvariant μG]
  [CompactSpace (Induction.LeftQuotient P)]

/-- The genuine induced distribution at the trivial parameter is that of the
original normalized induction. No equality of bundled carriers is assumed. -/
theorem normalizedUnramifiedInductionDistribution_one
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    normalizedUnramifiedInductionDistribution h hU hproj μG ν A hA 1 =
      Character.distribution μG ((normalizedInductionFunctor h hU).obj A).representation
        (normalizedInductionFunctor_obj_isAdmissible h hU hproj A hA) := by
  let E := SmoothRep.equivOfIso (normalizedUnramifiedInductionTrivialTwistIso h hU ν A)
  exact Character.distribution_eq_of_equivariant μG _ _ _ _
    E.toLinearEquiv E.toIntertwiningMap.isIntertwining

end Distribution

variable [MeasurableSpace G] [BorelSpace G] [T2Space G]
  (hproj : Continuous h.projection)
  (μG : Measure G) [μG.IsHaarMeasure] [μG.Regular]
  [CompactSpace (Induction.LeftQuotient P)]
  (hP : IsClosed (P : Set G))

include hP in
/-- Equality of genuine normalized induced distributions on an explicitly dense
unramified family implies equality of the original exact finite-length classes.
All finite-length and admissibility premises are retained. -/
theorem normalizedInductionClass_eq_of_dense
    (hAdm : ∀ (C : SmoothRep.{0, uG, max uG uV} ℂ G),
      C.HasFiniteLength → C.IsAdmissible)
    (hν : ∀ j, Continuous (ν j))
    {Q N : Subgroup G} (h' : IsSemidirectDecomposition Q M N)
    (hN : IsClosed (N : Set G)) (hproj' : Continuous h'.projection)
    (hQ : IsClosed (Q : Set G)) [CompactSpace (Induction.LeftQuotient Q)]
    (A B : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) (hB : B.IsAdmissible)
    (hAfl : ((normalizedInductionFunctor h hU).obj A).HasFiniteLength)
    (hBfl : ((normalizedInductionFunctor h' hN).obj B).HasFiniteLength)
    (S : Set (unramifiedCharacters ν)) (hS : Dense S)
    (hEq : ∀ χ ∈ S,
      normalizedUnramifiedInductionDistribution h hU hproj μG ν A hA χ =
        normalizedUnramifiedInductionDistribution h' hN hproj' μG ν B hB χ) :
    SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor h hU).obj A) hAfl =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor h' hN).obj B) hBfl := by
  apply (Character.ofRepresentation_eq_iff_distribution_eq μG hAdm _ _ hAfl hBfl
    (normalizedInductionFunctor_obj_isAdmissible h hU hproj A hA)
    (normalizedInductionFunctor_obj_isAdmissible h' hN hproj' B hB)).mpr
  have heq := normalizedUnramifiedInductionDistribution_eq_of_dense
    h hU hproj μG hP ν hν h' hN hproj' hQ A hA B hB S hS hEq 1
  simpa only [normalizedUnramifiedInductionDistribution_one] using heq

end Langlands.Aubert.General
