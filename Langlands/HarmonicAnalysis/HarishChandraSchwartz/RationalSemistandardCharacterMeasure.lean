import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.Representation.Plancherel.StandardLeviCharacterMeasure

/-! # Source-normalized measures on every actual semistandard Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (m : LeviModel p)

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance modelAffineHom : IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
local instance modelAffine : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
local instance modelSmooth : Smooth m.scheme.X.hom := m.reductive.smooth
local instance modelFiniteType : LocallyOfFiniteType m.scheme.X.hom := inferInstance
local instance modelTopology : TopologicalSpace (rationalPoints m.scheme) :=
  rationalPointTopology F m.scheme.X
local instance modelNonarchimedean : NonarchimedeanGroup (rationalPoints m.scheme) :=
  rationalPoints_nonarchimedeanGroup m.scheme

set_option hygiene false in
local notation "𝐌" => levi p
set_option hygiene false in
local notation "𝐋" => m.scheme
set_option hygiene false in
local notation "νM" => m.normCharacters
set_option hygiene false in
local notation "νL" => (fun ψ => (rationalNormCharacters 𝐋 ψ).toMul)
set_option hygiene false in
local notation "eM" => m.pointHomeomorph
set_option hygiene false in
local notation "eX" => unitaryCharacterHomeomorph m

/-- The canonical intrinsic-to-literal character homeomorphism, with the literal norm family. -/
def unitaryCharacterHomeomorph :
    unitaryUnramifiedCharacters νL ≃ₜ* unitaryUnramifiedCharacters νM :=
  unitaryUnramifiedCharactersHomeomorph eM νL

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- Waldspurger I.1's character measure, transported to the literal Levi. -/
def unitaryCharacterHaar :
    Measure (unitaryUnramifiedCharacters νM) :=
  Measure.map eX (rationalUnitaryUnramifiedCharacterHaar s
    hs.isCentralSplitTorus.isCentral hindex)

instance isHaarMeasure_unitaryCharacterHaar :
    (unitaryCharacterHaar m s hs hindex).IsHaarMeasure :=
  (eX).isHaarMeasure_map _

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem unitaryCharacterHaar_univ :
    unitaryCharacterHaar m s hs hindex Set.univ =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) := by
  unfold unitaryCharacterHaar
  rw [Measure.map_apply (f := fun z => eX z) (by fun_prop) MeasurableSet.univ]
  exact rationalUnitaryUnramifiedCharacterHaar_univ s hs.isCentralSplitTorus.isCentral hindex

instance isFiniteMeasure_unitaryCharacterHaar :
    IsFiniteMeasure (unitaryCharacterHaar m s hs hindex) := by
  refine ⟨?_⟩
  rw [unitaryCharacterHaar_univ]
  simp

variable [(m.splitCenter s).Normal] [(rationalPoints.map s).range.Normal]
local instance intrinsicQuotientMeasurable :
    MeasurableSpace (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) := borel _
local instance intrinsicQuotientBorel :
    BorelSpace (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) := ⟨rfl⟩

variable [MeasurableSpace (𝐌 ⧸ m.splitCenter s)]
  [BorelSpace (𝐌 ⧸ m.splitCenter s)]
  (mu : Measure (𝐌 ⧸ m.splitCenter s)) [mu.IsHaarMeasure]

/-- The central quotient identification induced by the actual Levi homeomorphism. -/
def centralQuotientHomeomorph :
    (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) ≃ₜ*
      (𝐌 ⧸ m.splitCenter s) :=
  quotientContinuousMulEquiv eM (m.splitCenter s) (rationalPoints.map s).range rfl

/-- The intrinsic quotient Haar measure corresponding to the displayed literal quotient Haar. -/
def intrinsicQuotientHaar :
    Measure (rationalPoints 𝐋 ⧸ (rationalPoints.map s).range) :=
  Measure.map (centralQuotientHomeomorph m s).symm mu

instance isHaarMeasure_intrinsicQuotientHaar :
    (intrinsicQuotientHaar m s mu).IsHaarMeasure :=
  (centralQuotientHomeomorph m s).symm.isHaarMeasure_map mu

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine T.X.left] [mu.IsHaarMeasure] in
@[simp]
theorem map_intrinsicQuotientHaar :
    Measure.map (centralQuotientHomeomorph m s)
      (intrinsicQuotientHaar m s mu) = mu :=
  MeasurableEquiv.map_map_symm
    (centralQuotientHomeomorph m s).toHomeomorph.toMeasurableEquiv

set_option hygiene false in
local notation "CM" => m.splitCenter s
set_option hygiene false in
local notation "hCM" => m.splitCenter_le_center s hs
set_option hygiene false in
local notation "CL" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hCL" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "muL" => intrinsicQuotientHaar m s mu

/-- Auxiliary pullback of a discrete-series class; the inducing representation stays on the literal semistandard Levi. -/
def intrinsicDiscreteSeriesClass (omega : DiscreteSeriesClass.{u, uV} CM hCM mu) :
    DiscreteSeriesClass.{u, uV} CL hCL muL :=
  DiscreteSeriesClass.pullback eM CM hCM CL hCL rfl mu muL
    (map_intrinsicQuotientHaar m s mu) omega

variable (omega : DiscreteSeriesClass.{u, uV} CM hCM mu)
set_option hygiene false in
local notation "omegaL" => intrinsicDiscreteSeriesClass m s hs mu omega
set_option hygiene false in
local notation "SM" => discreteSeriesStabilizer CM hCM mu νM omega
set_option hygiene false in
local notation "SL" => discreteSeriesStabilizer CL hCL muL νL omegaL

omit [IsAffine T.X.left] in
/-- Self-twists correspond under the canonical character homeomorphism. -/
theorem characterHomeomorph_map_stabilizer :
    (SL).map (eX).toMulEquiv.toMonoidHom = SM := by
  have equivariance (z : unitaryUnramifiedCharacters νM) :
      intrinsicDiscreteSeriesClass m s hs mu (z • omega) =
        (eX).symm z • omegaL :=
    DiscreteSeriesClass.pullback_smul eM νM νL
      (fun ψ x => congrArg ((rationalNormCharacters m.scheme ψ).toMul) (m.pointHomeomorph.symm_apply_apply x))
      CM hCM CL hCL rfl mu muL (map_intrinsicQuotientHaar m s mu) z omega
  have hinj := DiscreteSeriesClass.pullback_injective eM CM hCM CL hCL rfl mu muL
    (map_intrinsicQuotientHaar m s mu)
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change eX w • omega = omega
    apply hinj
    change intrinsicDiscreteSeriesClass m s hs mu (eX w • omega) = omegaL
    rw [equivariance, (eX).symm_apply_apply]
    exact hw
  · intro hz
    refine ⟨(eX).symm z, ?_, (eX).apply_symm_apply z⟩
    change (eX).symm z • omegaL = omegaL
    rw [← equivariance]
    exact congrArg (intrinsicDiscreteSeriesClass m s hs mu) hz

omit [IsAffine T.X.left] in
/-- The two finite self-twist groups have exactly the same cardinality. -/
theorem stabilizer_card : Nat.card SM = Nat.card SL := by
  let e := ((SL).equivMapOfInjective (eX).toMulEquiv.toMonoidHom (eX).injective).trans
    (MulEquiv.subgroupCongr (characterHomeomorph_map_stabilizer m s hs mu omega))
  exact (Nat.card_congr e.toEquiv).symm

include hindex in
theorem finite_literalDiscreteSeriesStabilizer : Finite SM := by
  let := finite_rationalDiscreteSeriesStabilizer s hs.isCentralSplitTorus.isCentral muL hindex omegaL
  let e := ((SL).equivMapOfInjective (eX).toMulEquiv.toMonoidHom (eX).injective).trans
    (MulEquiv.subgroupCongr (characterHomeomorph_map_stabilizer m s hs mu omega))
  exact Finite.of_surjective e e.surjective

/-- Identification of the actual twist orbits through the finite self-twist quotients. -/
def orbitHomeomorph :
    discreteSeriesOrbit CL hCL muL νL omegaL ≃ₜ discreteSeriesOrbit CM hCM mu νM omega :=
  (discreteSeriesOrbitHomeomorph CL hCL muL νL omegaL).symm.trans
    ((quotientContinuousMulEquiv eX SM SL
      (characterHomeomorph_map_stabilizer m s hs mu omega)).toHomeomorph.trans
        (discreteSeriesOrbitHomeomorph CM hCM mu νM omega))

omit [IsAffine T.X.left] in
@[simp]
theorem orbitHomeomorph_orbitMap
    (z : unitaryUnramifiedCharacters νL) :
    orbitHomeomorph m s hs mu omega
      (discreteSeriesOrbitMap CL hCL muL νL omegaL z) =
        discreteSeriesOrbitMap CM hCM mu νM omega (eX z) := by
  simp only [orbitHomeomorph, discreteSeriesOrbitMap,
    Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rfl

/-- I.1/VI.3's orbit measure, transported from the intrinsic Levi construction. -/
def normalizedOrbitMeasure :
    Measure (discreteSeriesOrbit CM hCM mu νM omega) :=
  Measure.map (orbitHomeomorph m s hs mu omega)
    (rationalNormalizedDiscreteSeriesOrbitMeasure s hs.isCentralSplitTorus.isCentral
      muL hindex omegaL)

instance isFiniteMeasure_normalizedOrbitMeasure :
    IsFiniteMeasure (normalizedOrbitMeasure m s hs hindex mu omega) := by
  unfold normalizedOrbitMeasure
  infer_instance

variable [Finite SM]

/-- The transported measure is precisely the measure used by the existing wave-packet integral. -/
theorem normalizedOrbitMeasure_eq :
    normalizedOrbitMeasure m s hs hindex mu omega =
      discreteSeriesOrbitMeasure νM CM hCM mu omega
        (unitaryCharacterHaar m s hs hindex) := by
  ext E hE
  unfold normalizedOrbitMeasure
  rw [Measure.map_apply (orbitHomeomorph m s hs mu omega).continuous.measurable hE]
  change rationalDiscreteSeriesOrbitMeasure s hs.isCentralSplitTorus.isCentral muL hindex omegaL
    (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex)
    ((orbitHomeomorph m s hs mu omega) ⁻¹' E) = _
  rw [rationalDiscreteSeriesOrbitMeasure_apply s hs.isCentralSplitTorus.isCentral muL hindex
      omegaL _ _ ((orbitHomeomorph m s hs mu omega).continuous.measurable hE),
    discreteSeriesOrbitMeasure_apply _ _ _ _ _ _ hE,
    unitaryCharacterHaar,
    Measure.map_apply (f := fun z => eX z) (by fun_prop)
      ((continuous_discreteSeriesOrbitMap CM hCM mu νM omega).measurable hE),
    stabilizer_card m s hs mu omega]
  congr 2
  ext z
  simp only [Set.mem_preimage, orbitHomeomorph_orbitMap]

/-- The finite-fiber formula retains the source's character scale. -/
theorem normalizedOrbitMeasure_eq_smul_map :
    normalizedOrbitMeasure m s hs hindex mu omega =
      (Nat.card SM : ℝ≥0∞)⁻¹ • Measure.map (discreteSeriesOrbitMap CM hCM mu νM omega)
        (unitaryCharacterHaar m s hs hindex) := by
  rw [normalizedOrbitMeasure_eq]
  rfl

/-- The literal twisting map locally preserves the I.1/VI.3 measures. -/
theorem isLocallyMeasurePreserving_normalizedOrbitMap :
    IsLocallyMeasurePreserving (discreteSeriesOrbitMap CM hCM mu νM omega)
      (unitaryCharacterHaar m s hs hindex)
      (normalizedOrbitMeasure m s hs hindex mu omega) := by
  rw [normalizedOrbitMeasure_eq]
  exact isLocallyMeasurePreserving_discreteSeriesOrbitMap νM CM hCM mu omega _

/-- Exact VI.3 mass: restriction-kernel cardinality divided by self-twist cardinality. -/
@[simp]
theorem normalizedOrbitMeasure_univ :
    normalizedOrbitMeasure m s hs hindex mu omega Set.univ =
      (Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker : ℝ≥0∞) /
        (Nat.card SM : ℝ≥0∞) := by
  rw [normalizedOrbitMeasure_eq, discreteSeriesOrbitMeasure_univ,
    unitaryCharacterHaar_univ]
  rw [div_eq_mul_inv, mul_comm]

/-- Reuse of the intrinsic normalized-orbit finiteness theorem for the literal integral measure. -/
theorem isFiniteMeasure_literalOrbitMeasure :
    IsFiniteMeasure (discreteSeriesOrbitMeasure νM CM hCM mu omega
      (unitaryCharacterHaar m s hs hindex)) := by
  rw [← normalizedOrbitMeasure_eq m s hs hindex mu omega]
  infer_instance

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure
