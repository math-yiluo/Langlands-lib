import Langlands.Representation.Plancherel.RationalRestrictionKernel
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # Actual rational-point twist stabilizers -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Actual affine finite-type rational points have an open-subgroup identity
basis in the canonical point topology. -/
theorem rationalPoints_nonarchimedeanGroup :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) := by
  let := rationalPoint_isTopologicalGroup F G
  refine { is_nonarchimedean := ?_ }
  intro U hU
  obtain ⟨K, _, hKU⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig
      (GroupScheme.rationalPoints G)).mp
        (Langlands.BruhatTits.rationalPoint_isLocallyProfinite F G)).2 U hU
  exact ⟨K, hKU⟩

local instance : NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints T.toGrp) :=
  rationalPointTopology F T.X

/-- The actual full twist stabilizer embeds into the actual central
restriction kernel, with the original character unchanged. -/
def rationalUnramifiedTwistStabilizerEmbedding (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (omega : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GroupScheme.rationalPoints G)) :
    unramifiedTwistStabilizer (fun psi => (rationalNormCharacters G psi).toMul) omega ↪
      (rationalUnramifiedCharacterRestrict s).toMonoidHom.ker where
  toFun chi := ⟨chi.val, by
    rw [rationalUnramifiedCharacterRestrict_ker]
    exact unramifiedTwistStabilizer_le_centralTrivial
      (fun psi => (rationalNormCharacters G psi).toMul)
      (GroupScheme.rationalPoints.map s).range hs.range_le_center omega chi.property⟩
  inj' := by
    intro chi eta h
    exact Subtype.ext (congrArg
      (fun x : (rationalUnramifiedCharacterRestrict s).toMonoidHom.ker => x.val) h)

@[simp]
theorem rationalUnramifiedTwistStabilizerEmbedding_apply (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (omega : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GroupScheme.rationalPoints G))
    (chi : unramifiedTwistStabilizer
      (fun psi => (rationalNormCharacters G psi).toMul) omega)
    (g : GroupScheme.rationalPoints G) :
    (rationalUnramifiedTwistStabilizerEmbedding s hs omega chi).val.val g =
      chi.val.val g := rfl

/-- The full actual twist stabilizer is finite under the explicit
actual-image finite-index premise. -/
theorem finite_rationalUnramifiedTwistStabilizer (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (omega : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GroupScheme.rationalPoints G)) :
    Finite (unramifiedTwistStabilizer
      (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := finite_rationalUnramifiedCharacterRestrict_ker s hs hindex
  exact Finite.of_injective _ (rationalUnramifiedTwistStabilizerEmbedding s hs omega).injective

/-- Every character in the full actual twist stabilizer is unitary under
the same explicit premise. -/
theorem rationalUnramifiedTwistStabilizer_norm_eq_one (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (omega : SmoothDualClass.{0, u, uV} (k := ℂ) (G := GroupScheme.rationalPoints G))
    (chi : unramifiedTwistStabilizer
      (fun psi => (rationalNormCharacters G psi).toMul) omega)
    (g : GroupScheme.rationalPoints G) :
    ‖(chi.val.val g : ℂ)‖ = 1 :=
  rationalUnramifiedCharacterRestrict_ker_norm_eq_one s hs hindex
    (rationalUnramifiedTwistStabilizerEmbedding s hs omega chi) g

section DiscreteSeries

variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)

variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : MeasureTheory.Measure
  (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))

/-- The unitary orbit stabilizer and the full source stabilizer agree for
actual rational points, under the displayed finite-index premise. -/
def rationalDiscreteSeriesStabilizerEquivFull
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega ≃*
        unramifiedTwistStabilizer (fun psi => (rationalNormCharacters G psi).toMul) omega.val := by
  letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  let : Finite (GroupScheme.rationalPoints G ⧸
      (commonNormKernel (fun psi => (rationalNormCharacters G psi).toMul) ⊔
        (GroupScheme.rationalPoints.map s).range)) :=
    finite_rationalCentralQuotient s hs hindex
  exact discreteSeriesStabilizerEquivFull
    (fun psi => (rationalNormCharacters G psi).toMul)
    (GroupScheme.rationalPoints.map s).range hs.range_le_center mu omega

omit [IsAffine T.X.left] in
@[simp]
theorem rationalDiscreteSeriesStabilizerEquivFull_apply
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (chi : discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)
      (g : GroupScheme.rationalPoints G),
      (rationalDiscreteSeriesStabilizerEquivFull s hs mu hindex omega chi).val.val g =
        chi.val.val g := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega chi g
  rfl

/-- The actual unitary orbit stabilizer is finite. No finiteness of a
representation family or of the orbit space is assumed. -/
theorem finite_rationalDiscreteSeriesStabilizer
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      Finite (discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  let := finite_rationalUnramifiedTwistStabilizer s hs hindex omega.val
  exact Finite.of_injective _
    (rationalDiscreteSeriesStabilizerEquivFull s hs mu hindex omega).injective

end DiscreteSeries

end Langlands.Plancherel
