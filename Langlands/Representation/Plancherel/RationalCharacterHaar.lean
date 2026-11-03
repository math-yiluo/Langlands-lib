import Langlands.Representation.Plancherel.RationalRestrictionSurjectivity
import Langlands.Representation.Plancherel.RationalRestrictionKernel
import Langlands.Representation.Plancherel.RestrictionNormalizedHaar
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitMeasure

/-! # The I.1 Haar measure on actual unitary unramified characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology MeasureTheory MeasureTheory.Measure
open Langlands.AlgebraicGeometry.PointTopology Langlands.HarishChandraSchwartz
open scoped ENNReal NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalCharacterHaarGroupPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalCharacterHaarGroupCompactSpace : CompactSpace
    (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :=
  compactSpace_rationalUnitaryUnramifiedCharacters G

/-- Probability Haar measure on the actual compact unitary unramified character group. -/
def rationalUnitaryUnramifiedProbabilityHaar :
    Measure (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :=
  normalizedHaar _

instance instRationalCharacterHaar1 : IsHaarMeasure (rationalUnitaryUnramifiedProbabilityHaar G) := by
  unfold rationalUnitaryUnramifiedProbabilityHaar
  infer_instance

instance instRationalCharacterHaar2 : IsProbabilityMeasure (rationalUnitaryUnramifiedProbabilityHaar G) := by
  unfold rationalUnitaryUnramifiedProbabilityHaar
  infer_instance

@[simp]
theorem rationalUnitaryUnramifiedProbabilityHaar_univ :
    rationalUnitaryUnramifiedProbabilityHaar G Set.univ = 1 :=
  measure_univ

variable {G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffine T.X.left]

local instance rationalCharacterHaarTorusPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints T.toGrp) :=
  rationalPointTopology F T.X

/-- The actual character Haar measure with the finite-kernel restriction scale.
The finite-index premise concerns the actual central valuation image. -/
def rationalUnitaryUnramifiedCharacterHaar (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Measure (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) := by
  let := finite_rationalUnitaryUnramifiedCharacterRestrict_ker s hs hindex
  exact restrictionNormalizedHaar (rationalUnitaryUnramifiedCharacterRestrict s)

instance instRationalCharacterHaar3 (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    IsHaarMeasure (rationalUnitaryUnramifiedCharacterHaar s hs hindex) := by
  unfold rationalUnitaryUnramifiedCharacterHaar
  infer_instance

theorem rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability
    (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    rationalUnitaryUnramifiedCharacterHaar s hs hindex =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) •
        rationalUnitaryUnramifiedProbabilityHaar G := rfl

@[simp]
theorem rationalUnitaryUnramifiedCharacterHaar_apply
    (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (E : Set (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))) :
    rationalUnitaryUnramifiedCharacterHaar s hs hindex E =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) *
        rationalUnitaryUnramifiedProbabilityHaar G E := rfl

@[simp]
theorem rationalUnitaryUnramifiedCharacterHaar_univ
    (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    rationalUnitaryUnramifiedCharacterHaar s hs hindex Set.univ =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) := by
  simp

variable [LocallyOfFiniteType T.X.hom]

local instance rationalCharacterHaarTorusCompactSpace : CompactSpace
    (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters T.toGrp psi).toMul)) :=
  compactSpace_rationalUnitaryUnramifiedCharacters T.toGrp

/-- Actual restriction pushes the I.1 source measure to kernel-cardinality times
the split component's probability Haar measure. Surjectivity is proved. -/
theorem map_rationalUnitaryUnramifiedCharacterHaar
    (s : T.toGrp ⟶ G) (hG : GroupScheme.IsConnectedReductive G)
    (hs : GroupScheme.IsSplitComponent s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Measure.map (rationalUnitaryUnramifiedCharacterRestrict s)
      (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex) =
        (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) •
          rationalUnitaryUnramifiedProbabilityHaar T.toGrp := by
  let := finite_rationalUnitaryUnramifiedCharacterRestrict_ker s hs.isCentralSplitTorus.isCentral hindex
  exact map_restrictionNormalizedHaar (rationalUnitaryUnramifiedCharacterRestrict s)
    (rationalUnitaryUnramifiedCharacterRestrict_surjective s hG hs)

/-- Waldspurger I.1: actual restriction locally preserves the fixed character
measures, conditional only on the displayed actual-image finite-index premise. -/
theorem isLocallyMeasurePreserving_rationalUnitaryUnramifiedCharacterRestrict
    (s : T.toGrp ⟶ G) (hG : GroupScheme.IsConnectedReductive G)
    (hs : GroupScheme.IsSplitComponent s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    IsLocallyMeasurePreserving (rationalUnitaryUnramifiedCharacterRestrict s)
      (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex)
      (rationalUnitaryUnramifiedProbabilityHaar T.toGrp) := by
  let := finite_rationalUnitaryUnramifiedCharacterRestrict_ker s hs.isCentralSplitTorus.isCentral hindex
  exact isLocallyMeasurePreserving_restrictionNormalizedHaar
    (rationalUnitaryUnramifiedCharacterRestrict s)
    (rationalUnitaryUnramifiedCharacterRestrict_surjective s hG hs)

end Langlands.Plancherel
