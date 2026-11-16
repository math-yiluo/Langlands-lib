import Langlands.Representation.Plancherel.RationalOrbitIntegration
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket

/-! # I.1 character and orbit measures on the literal standard Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.HarishChandraSchwartz Langlands.Aubert.General

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (I : Finset (RationalPointFamily.SimpleRoot i ν))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "νL" => (fun ψ => (rationalNormCharacters 𝐋 ψ).toMul)
set_option hygiene false in
local notation "eM" => RationalPointFamily.leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "eX" => standardLeviUnitaryCharacterHomeomorph I

local instance standardLeviMeasureAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviMeasureAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviMeasureFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviMeasureTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviMeasureNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
  rationalPoints_nonarchimedeanGroup 𝐋

/-- The canonical intrinsic-to-literal character homeomorphism, with the literal norm family. -/
def standardLeviUnitaryCharacterHomeomorph :
    unitaryUnramifiedCharacters νL ≃ₜ* unitaryUnramifiedCharacters νM :=
  unitaryUnramifiedCharactersHomeomorph eM νL

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- Waldspurger I.1's character measure, transported to the literal Levi. -/
def standardLeviUnitaryUnramifiedCharacterHaar :
    Measure (unitaryUnramifiedCharacters νM) :=
  Measure.map eX (rationalUnitaryUnramifiedCharacterHaar s
    hs.isCentralSplitTorus.isCentral hindex)

instance isHaarMeasure_standardLeviUnitaryUnramifiedCharacterHaar :
    (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex).IsHaarMeasure :=
  (eX).isHaarMeasure_map _

@[simp]
theorem standardLeviUnitaryUnramifiedCharacterHaar_univ :
    standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex Set.univ =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) := by
  unfold standardLeviUnitaryUnramifiedCharacterHaar
  rw [Measure.map_apply (f := fun z => eX z) (by fun_prop) MeasurableSet.univ]
  exact rationalUnitaryUnramifiedCharacterHaar_univ s hs.isCentralSplitTorus.isCentral hindex

instance isFiniteMeasure_standardLeviUnitaryUnramifiedCharacterHaar :
    IsFiniteMeasure (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex) := by
  refine ⟨?_⟩
  rw [standardLeviUnitaryUnramifiedCharacterHaar_univ]
  simp

variable [(rationalLeviSplitCenter I s).Normal] [(rationalPoints.map s).range.Normal]
local instance standardLeviMeasureIntrinsicQuotientMeasurable :
    MeasurableSpace (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) := borel _
local instance standardLeviMeasureIntrinsicQuotientBorel :
    BorelSpace (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) := ⟨rfl⟩

variable [MeasurableSpace (𝐌 ⧸ rationalLeviSplitCenter I s)]
  [BorelSpace (𝐌 ⧸ rationalLeviSplitCenter I s)]
  (mu : Measure (𝐌 ⧸ rationalLeviSplitCenter I s)) [mu.IsHaarMeasure]

/-- The central quotient identification induced by the actual Levi homeomorphism. -/
def standardLeviCentralQuotientHomeomorph :
    (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) ≃ₜ*
      (𝐌 ⧸ rationalLeviSplitCenter I s) :=
  quotientContinuousMulEquiv eM (rationalLeviSplitCenter I s) (rationalPoints.map s).range rfl

/-- The intrinsic quotient Haar measure corresponding to the displayed literal quotient Haar. -/
def standardLeviIntrinsicQuotientHaar :
    Measure (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) :=
  Measure.map (standardLeviCentralQuotientHomeomorph I s).symm mu

instance isHaarMeasure_standardLeviIntrinsicQuotientHaar :
    (standardLeviIntrinsicQuotientHaar I s mu).IsHaarMeasure :=
  (standardLeviCentralQuotientHomeomorph I s).symm.isHaarMeasure_map mu

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine T.X.left] [mu.IsHaarMeasure] in
@[simp]
theorem map_standardLeviIntrinsicQuotientHaar :
    Measure.map (standardLeviCentralQuotientHomeomorph I s)
      (standardLeviIntrinsicQuotientHaar I s mu) = mu :=
  MeasurableEquiv.map_map_symm
    (standardLeviCentralQuotientHomeomorph I s).toHomeomorph.toMeasurableEquiv

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs
set_option hygiene false in
local notation "CL" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hCL" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "muL" => standardLeviIntrinsicQuotientHaar I s mu

/-- Auxiliary pullback of a discrete-series class; the inducing representation stays on `M_I(F)`. -/
def standardLeviIntrinsicDiscreteSeriesClass (omega : DiscreteSeriesClass.{u, uV} CM hCM mu) :
    DiscreteSeriesClass.{u, uV} CL hCL muL :=
  DiscreteSeriesClass.pullback eM CM hCM CL hCL rfl mu muL
    (map_standardLeviIntrinsicQuotientHaar I s mu) omega

variable (omega : DiscreteSeriesClass.{u, uV} CM hCM mu)
set_option hygiene false in
local notation "omegaL" => standardLeviIntrinsicDiscreteSeriesClass I s hs mu omega
set_option hygiene false in
local notation "SM" => discreteSeriesStabilizer CM hCM mu νM omega
set_option hygiene false in
local notation "SL" => discreteSeriesStabilizer CL hCL muL νL omegaL

omit [IsAffine T.X.left] in
/-- Self-twists correspond under the canonical character homeomorphism. -/
theorem standardLeviCharacterHomeomorph_map_stabilizer :
    (SL).map (eX).toMulEquiv.toMonoidHom = SM := by
  have equivariance (z : unitaryUnramifiedCharacters νM) :
      standardLeviIntrinsicDiscreteSeriesClass I s hs mu (z • omega) =
        (eX).symm z • omegaL :=
    DiscreteSeriesClass.pullback_smul eM νM νL
      (fun ψ m => RationalPointFamily.leviRationalNormCharacters_apply_points i ν I ψ m)
      CM hCM CL hCL rfl mu muL (map_standardLeviIntrinsicQuotientHaar I s mu) z omega
  have hinj := DiscreteSeriesClass.pullback_injective eM CM hCM CL hCL rfl mu muL
    (map_standardLeviIntrinsicQuotientHaar I s mu)
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change eX w • omega = omega
    apply hinj
    change standardLeviIntrinsicDiscreteSeriesClass I s hs mu (eX w • omega) = omegaL
    rw [equivariance, (eX).symm_apply_apply]
    exact hw
  · intro hz
    refine ⟨(eX).symm z, ?_, (eX).apply_symm_apply z⟩
    change (eX).symm z • omegaL = omegaL
    rw [← equivariance]
    exact congrArg (standardLeviIntrinsicDiscreteSeriesClass I s hs mu) hz

omit [IsAffine T.X.left] in
/-- The two finite self-twist groups have exactly the same cardinality. -/
theorem standardLeviStabilizer_card : Nat.card SM = Nat.card SL := by
  let e := ((SL).equivMapOfInjective (eX).toMulEquiv.toMonoidHom (eX).injective).trans
    (MulEquiv.subgroupCongr (standardLeviCharacterHomeomorph_map_stabilizer I s hs mu omega))
  exact (Nat.card_congr e.toEquiv).symm

include hindex in
theorem finite_standardLeviDiscreteSeriesStabilizer : Finite SM := by
  let := finite_rationalDiscreteSeriesStabilizer s hs.isCentralSplitTorus.isCentral muL hindex omegaL
  let e := ((SL).equivMapOfInjective (eX).toMulEquiv.toMonoidHom (eX).injective).trans
    (MulEquiv.subgroupCongr (standardLeviCharacterHomeomorph_map_stabilizer I s hs mu omega))
  exact Finite.of_surjective e e.surjective

/-- Identification of the actual twist orbits through the finite self-twist quotients. -/
def standardLeviDiscreteSeriesOrbitHomeomorph :
    discreteSeriesOrbit CL hCL muL νL omegaL ≃ₜ discreteSeriesOrbit CM hCM mu νM omega :=
  (discreteSeriesOrbitHomeomorph CL hCL muL νL omegaL).symm.trans
    ((quotientContinuousMulEquiv eX SM SL
      (standardLeviCharacterHomeomorph_map_stabilizer I s hs mu omega)).toHomeomorph.trans
        (discreteSeriesOrbitHomeomorph CM hCM mu νM omega))

omit [IsAffine T.X.left] in
@[simp]
theorem standardLeviDiscreteSeriesOrbitHomeomorph_orbitMap
    (z : unitaryUnramifiedCharacters νL) :
    standardLeviDiscreteSeriesOrbitHomeomorph I s hs mu omega
      (discreteSeriesOrbitMap CL hCL muL νL omegaL z) =
        discreteSeriesOrbitMap CM hCM mu νM omega (eX z) := by
  simp only [standardLeviDiscreteSeriesOrbitHomeomorph, discreteSeriesOrbitMap,
    Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rfl

/-- I.1/VI.3's orbit measure, transported from the intrinsic Levi construction. -/
def standardLeviNormalizedDiscreteSeriesOrbitMeasure :
    Measure (discreteSeriesOrbit CM hCM mu νM omega) :=
  Measure.map (standardLeviDiscreteSeriesOrbitHomeomorph I s hs mu omega)
    (rationalNormalizedDiscreteSeriesOrbitMeasure s hs.isCentralSplitTorus.isCentral
      muL hindex omegaL)

instance isFiniteMeasure_standardLeviNormalizedDiscreteSeriesOrbitMeasure :
    IsFiniteMeasure (standardLeviNormalizedDiscreteSeriesOrbitMeasure I s hs hindex mu omega) := by
  unfold standardLeviNormalizedDiscreteSeriesOrbitMeasure
  infer_instance

variable [Finite SM]

/-- The transported measure is precisely the measure used by the existing wave-packet integral. -/
theorem standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq :
    standardLeviNormalizedDiscreteSeriesOrbitMeasure I s hs hindex mu omega =
      discreteSeriesOrbitMeasure νM CM hCM mu omega
        (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex) := by
  ext E hE
  unfold standardLeviNormalizedDiscreteSeriesOrbitMeasure
  rw [Measure.map_apply (standardLeviDiscreteSeriesOrbitHomeomorph I s hs mu omega).continuous.measurable hE]
  change rationalDiscreteSeriesOrbitMeasure s hs.isCentralSplitTorus.isCentral muL hindex omegaL
    (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex)
    ((standardLeviDiscreteSeriesOrbitHomeomorph I s hs mu omega) ⁻¹' E) = _
  rw [rationalDiscreteSeriesOrbitMeasure_apply s hs.isCentralSplitTorus.isCentral muL hindex
      omegaL _ _ ((standardLeviDiscreteSeriesOrbitHomeomorph I s hs mu omega).continuous.measurable hE),
    discreteSeriesOrbitMeasure_apply _ _ _ _ _ _ hE,
    standardLeviUnitaryUnramifiedCharacterHaar,
    Measure.map_apply (f := fun z => eX z) (by fun_prop)
      ((continuous_discreteSeriesOrbitMap CM hCM mu νM omega).measurable hE),
    standardLeviStabilizer_card I s hs mu omega]
  congr 2
  ext z
  simp only [Set.mem_preimage, standardLeviDiscreteSeriesOrbitHomeomorph_orbitMap]

/-- The finite-fiber formula retains the source's character scale. -/
theorem standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq_smul_map :
    standardLeviNormalizedDiscreteSeriesOrbitMeasure I s hs hindex mu omega =
      (Nat.card SM : ℝ≥0∞)⁻¹ • Measure.map (discreteSeriesOrbitMap CM hCM mu νM omega)
        (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex) := by
  rw [standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq]
  rfl

/-- The literal twisting map locally preserves the I.1/VI.3 measures. -/
theorem isLocallyMeasurePreserving_standardLeviNormalizedDiscreteSeriesOrbitMap :
    IsLocallyMeasurePreserving (discreteSeriesOrbitMap CM hCM mu νM omega)
      (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex)
      (standardLeviNormalizedDiscreteSeriesOrbitMeasure I s hs hindex mu omega) := by
  rw [standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq]
  exact isLocallyMeasurePreserving_discreteSeriesOrbitMap νM CM hCM mu omega _

/-- Exact VI.3 mass: restriction-kernel cardinality divided by self-twist cardinality. -/
@[simp]
theorem standardLeviNormalizedDiscreteSeriesOrbitMeasure_univ :
    standardLeviNormalizedDiscreteSeriesOrbitMeasure I s hs hindex mu omega Set.univ =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) /
        (Nat.card SM : ℝ≥0∞) := by
  rw [standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq, discreteSeriesOrbitMeasure_univ,
    standardLeviUnitaryUnramifiedCharacterHaar_univ]
  rw [div_eq_mul_inv, mul_comm]

/-- Reuse of the intrinsic normalized-orbit finiteness theorem for the literal integral measure. -/
theorem isFiniteMeasure_standardLeviOrbitMeasure :
    IsFiniteMeasure (discreteSeriesOrbitMeasure νM CM hCM mu omega
      (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex)) := by
  rw [← standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq I s hs hindex mu omega]
  infer_instance

end Langlands.Plancherel
