import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Induction.CompactQuotientTwistTrace
import Langlands.Representation.Induction.UnramifiedCompactStabilizer
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.CompactOpen

/-! Actual normalized induction, admissibility and unramified trace coefficients. -/

noncomputable section

namespace Langlands.Aubert.General

open HarmonicAnalysis MeasureTheory Plancherel Topology
open scoped NNReal

universe uG uV uI uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)

section Projection
variable [IsTopologicalGroup G]

/-- The actual Levi projection is open whenever it is continuous. -/
theorem IsSemidirectDecomposition.isOpenMap_projection
    (hproj : Continuous h.projection) : IsOpenMap h.projection := by
  have hs : Continuous (Subgroup.inclusion h.levi_le) :=
    continuous_subtype_val.subtype_mk _
  exact (MonoidHom.isOpenQuotientMap_of_isQuotientMap
    (IsQuotientMap.of_inverse hs hproj (fun m => h.projection_levi m))).isOpenMap

end Projection

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]
variable (hU : IsClosed (U : Set G)) (hproj : Continuous h.projection)

/-- A Levi twist pulls back through the actual projection and commutes with the
fixed half-modulus normalization. -/
theorem inducingRepresentation_twist
    (A : SmoothRep.{0, uG, uV} ℂ M) (χ : M →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set M)) :
    inducingRepresentation h hU (A.twist χ hχ) =
      Langlands.twist (χ.comp h.projection) (inducingRepresentation h hU A) := by
  ext p v
  change (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
      ((χ (h.projection p) : ℂ) • A.representation (h.projection p) v) =
    (χ (h.projection p) : ℂ) •
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
        A.representation (h.projection p) v)
  exact smul_comm _ _ _

variable [MeasurableSpace G] [BorelSpace G] [T2Space G]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [Measure.IsMulLeftInvariant μ]
variable (hP : IsClosed (P : Set G)) [CompactSpace (Induction.LeftQuotient P)]

/-- One finite coefficient function for every unramified twist of actual
normalized induction. It is chosen independently of the norm family. -/
def normalizedInductionTwistCoefficients
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) (f : SchwartzBruhat G) : P →₀ ℂ :=
  Induction.compactQuotientTwistCoefficients μ P hP (inducingRepresentation h hU A)
    (inducingRepresentation_isAdmissible h hU hproj A hA) f

variable {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- The actual distribution of normalized induction of an unramified twist,
with admissibility derived from that of the original Levi representation. -/
def normalizedUnramifiedInductionDistribution
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (χ : unramifiedCharacters ν) : Distribution G :=
  Character.distribution μ
    ((normalizedInductionFunctor h hU).obj
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation
    (normalizedInductionFunctor_obj_isAdmissible h hU hproj _
      ((SmoothRep.isAdmissible_twist_iff χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ) A).mpr hA))

set_option maxHeartbeats 2000000 in
/-- The coefficient formula computes the genuine normalized distribution at
all unramified parameters, using continuity of each positive norm character. -/
theorem normalizedUnramifiedInductionDistribution_eval
    (hν : ∀ i, Continuous (ν i))
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (χ : unramifiedCharacters ν) (f : SchwartzBruhat G) :
    normalizedUnramifiedInductionDistribution h hU hproj μ ν A hA χ f =
      Finsupp.linearCombination ℂ (fun p : P => (χ.val (h.projection p) : ℂ))
        (normalizedInductionTwistCoefficients h hU hproj μ hP A hA f) := by
  have he := inducingRepresentation_twist h hU A χ.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker ν χ)
  have hAdm : IsAdmissible (Induction.smoothInduced P
      (Langlands.twist (χ.val.toMonoidHom.comp h.projection)
        (inducingRepresentation h hU A))) := by
    rw [← he]
    exact normalizedInductionFunctor_obj_isAdmissible h hU hproj _
      ((SmoothRep.isAdmissible_twist_iff χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν χ) A).mpr hA)
  have htransport (σ τ : Representation ℂ P A) (e : σ = τ)
      (hσ : IsAdmissible (Induction.smoothInduced P σ))
      (hτ : IsAdmissible (Induction.smoothInduced P τ)) :
      Character.distribution μ (Induction.smoothInduced P σ) hσ =
        Character.distribution μ (Induction.smoothInduced P τ) hτ := by
    subst τ
    rfl
  calc
    _ = Character.distribution μ (Induction.smoothInduced P
        (Langlands.twist (χ.val.toMonoidHom.comp h.projection)
          (inducingRepresentation h hU A))) hAdm f :=
      congrArg (fun D : Distribution G => D f) (htransport _ _ he _ hAdm)
    _ = _ := Induction.compactQuotientTwistCoefficients_eval μ P hP
      (inducingRepresentation h hU A) (inducingRepresentation_isAdmissible h hU hproj A hA)
      f (χ.val.toMonoidHom.comp h.projection)
      (Induction.compactSubgroup_le_unramifiedPullback_ker ν hν h.projection hproj χ) hAdm

include hP in
/-- Actual normalized induced distribution values are continuous on the actual
unramified character group with its inherited compact-open topology. -/
theorem continuous_normalizedUnramifiedInductionDistribution
    (hν : ∀ i, Continuous (ν i))
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (f : SchwartzBruhat G) :
    Continuous (fun χ : unramifiedCharacters ν =>
      normalizedUnramifiedInductionDistribution h hU hproj μ ν A hA χ f) := by
  let c := normalizedInductionTwistCoefficients h hU hproj μ hP A hA f
  have he : (fun χ : unramifiedCharacters ν =>
      normalizedUnramifiedInductionDistribution h hU hproj μ ν A hA χ f) =
      (fun χ => ∑ p ∈ c.support, c p * (χ.val (h.projection p) : ℂ)) := by
    funext χ
    rw [normalizedUnramifiedInductionDistribution_eval h hU hproj μ hP ν hν A hA χ f]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
    rfl
  rw [he]
  exact continuous_finsetSum _ (fun p _ =>
    continuous_const.mul (Units.continuous_val.comp
      ((continuous_eval_const (h.projection p)).comp continuous_subtype_val)))

include hP in
/-- For two actual normalized inductions with the same Levi and norm family,
equality on an explicitly dense set of unramified characters extends everywhere. -/
theorem normalizedUnramifiedInductionDistribution_eq_of_dense
    (hν : ∀ i, Continuous (ν i))
    {Q N : Subgroup G} (h' : IsSemidirectDecomposition Q M N)
    (hN : IsClosed (N : Set G)) (hproj' : Continuous h'.projection)
    (hQ : IsClosed (Q : Set G)) [CompactSpace (Induction.LeftQuotient Q)]
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (B : SmoothRep.{0, uG, uW} ℂ M) (hB : B.IsAdmissible)
    (S : Set (unramifiedCharacters ν)) (hS : Dense S)
    (hEq : ∀ χ ∈ S,
      normalizedUnramifiedInductionDistribution h hU hproj μ ν A hA χ =
        normalizedUnramifiedInductionDistribution h' hN hproj' μ ν B hB χ) :
    ∀ χ, normalizedUnramifiedInductionDistribution h hU hproj μ ν A hA χ =
      normalizedUnramifiedInductionDistribution h' hN hproj' μ ν B hB χ := by
  intro χ
  ext f
  have hcA := continuous_normalizedUnramifiedInductionDistribution h hU hproj μ hP ν hν
    A hA f
  have hcB := continuous_normalizedUnramifiedInductionDistribution h' hN hproj' μ hQ ν hν
    B hB f
  have hclosed := isClosed_eq hcA hcB
  have hclosure : closure S ⊆ {χ |
      normalizedUnramifiedInductionDistribution h hU hproj μ ν A hA χ f =
        normalizedUnramifiedInductionDistribution h' hN hproj' μ ν B hB χ f} :=
    hclosed.closure_subset_iff.mpr (fun χ hχ =>
      congrArg (fun D : Distribution G => D f) (hEq χ hχ))
  exact hclosure (hS χ)

end Langlands.Aubert.General
