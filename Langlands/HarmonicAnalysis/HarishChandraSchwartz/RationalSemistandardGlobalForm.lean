import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralAction
import Langlands.Representation.Plancherel.ProductInducedOrbitForm
import Langlands.Representation.Plancherel.ProductInducedOrbitFullAction

/-! # Actual integral global form on semistandard spectral families -/

noncomputable section

universe u uV uI

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

namespace FiniteSupportSections

section SesquilinearTotal

variable {I : Type uI} {V : I → Type uV} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)] (W : ∀ i, Submodule ℂ (V i))
  (B : ∀ i, W i →ₗ⋆[ℂ] W i →ₗ[ℂ] ℂ)

/-- The finite-support sum of the specified actual sesquilinear summands. -/
def totalSesquilinear : submodule W →ₗ⋆[ℂ] submodule W →ₗ[ℂ] ℂ where
  toFun f := totalLinear W (fun i => B i (component W i f))
  map_add' f g := by
    apply LinearMap.ext
    intro h
    change (∑ᶠ i, B i (component W i (f + g)) (component W i h)) = _
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib
      (linearSummand_finite W (fun i => B i (component W i f)) h)
      (linearSummand_finite W (fun i => B i (component W i g)) h)
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    change (∑ᶠ i, B i (component W i (c • f)) (component W i g)) = _
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply]
    exact (smul_finsum' ((starRingEnd ℂ) c)
      (linearSummand_finite W (fun i => B i (component W i f)) g)).symm

end SesquilinearTotal

end FiniteSupportSections

namespace RationalSemistandard

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean


variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {t : SemistandardSpectralIndex i} (hG : IsConnectedReductive G)
  (model : LeviModel t) (r : CocharacterPresentation hG t) (d : CompactData t)

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance formLeviLocallyCompact : LocallyCompactSpace (levi t) :=
  (isClosed_levi_of_model (chosenLeviModel t)).locallyCompactSpace
local instance formParabolicLocallyCompact : LocallyCompactSpace (parabolic t) :=
  (isClosed_parabolic t).locallyCompactSpace

include model d in
/-- Intersect the actual compact picture with the exact closed literal Levi. -/
theorem compactOpenCofinal_levi : CompactOpenCofinal (levi t) := by
  let L : OpenSubgroup (levi t) :=
    d.compact.comap (levi t).subtype continuous_subtype_val
  have hL : IsCompact (L : Set (levi t)) :=
    (isClosed_levi_of_model model).isClosedEmbedding_subtypeVal.isCompact_preimage d.isCompact
  have : Nonempty (CompactOpenSubgroup (levi t)) := ⟨⟨L, hL⟩⟩
  exact CompactOpenSubgroup.cofinal

namespace SourceForm

section Pairing

variable (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t))
  (C : Subgroup (levi t)) [C.Normal] (hC : C ≤ Subgroup.center (levi t))
  [MeasurableSpace (levi t ⧸ C)] [BorelSpace (levi t ⧸ C)]
  (mu : Measure (levi t ⧸ C)) [mu.IsHaarMeasure] [mu.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation mu)

/-- The actual inverse-formal-degree induced tensor form at each representative. -/
def representativeForm (A : UnitaryOrbitRepresentative model.normCharacters pi) :=
  unitaryOrbitRepresentativeProductForm (decomposition t) (isClosed_radical t)
    (isClosed_parabolic t) d.compact d.isCompact d.factorization
    (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d)
    pi (compactOpenCofinal_levi model d) C hC mu hsq model.normCharacters A

/-- The existing actual inverse-degree pairing, conjugate linear in its first argument. -/
def pairing (v w : smoothOrbitSections model d pi)
    (omega : discreteSeriesOrbit C hC mu model.normCharacters (discreteSeriesClass C hC mu pi hsq)) : ℂ :=
  unitaryOrbitProductPairing (decomposition t) (isClosed_radical t) (isClosed_parabolic t)
    d.compact d.isCompact d.factorization (ambient_modularCharacter hG)
    (parabolic_modularCharacter hG model r d) pi (compactOpenCofinal_levi model d)
    C hC mu hsq model.normCharacters model.continuous_normCharacters d.projection_continuous
    model.unitaryCoordinates.toMulEquiv v w omega

/-- The orbit pairing is the same canonical form at every actual inducing representative. -/
theorem pairing_representative (v w : smoothOrbitSections model d pi)
    (A : UnitaryOrbitRepresentative model.normCharacters pi) :
    pairing hG model r d pi C hC mu hsq v w
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi C hC mu hsq A) =
      (representativeForm hG model r d pi C hC mu hsq A).inner (v.val A) (w.val A) :=
  unitaryOrbitProductPairing_representative (decomposition t) (isClosed_radical t)
    (isClosed_parabolic t) d.compact d.isCompact d.factorization
    (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d)
    pi (compactOpenCofinal_levi model d) C hC mu hsq model.normCharacters
    model.continuous_normCharacters d.projection_continuous model.unitaryCoordinates.toMulEquiv v w A

/-- Continuity holds in the actual orbit quotient topology. -/
theorem continuous_pairing (v w : smoothOrbitSections model d pi) :
    Continuous (pairing hG model r d pi C hC mu hsq v w) :=
  continuous_unitaryOrbitProductPairing (decomposition t) (isClosed_radical t)
    (isClosed_parabolic t) d.compact d.isCompact d.factorization
    (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d)
    pi (compactOpenCofinal_levi model d) C hC mu hsq model.normCharacters
    model.continuous_normCharacters d.projection_continuous model.unitaryCoordinates.toMulEquiv
    model.unitaryCoordinates.continuous v w

variable (v w z : smoothOrbitSections model d pi)
  (omega : discreteSeriesOrbit C hC mu model.normCharacters (discreteSeriesClass C hC mu pi hsq))

theorem pairing_add_left :
    pairing hG model r d pi C hC mu hsq (v + w) z omega =
      pairing hG model r d pi C hC mu hsq v z omega +
        pairing hG model r d pi C hC mu hsq w z omega := by
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
    model.normCharacters pi C hC mu hsq omega
  simp only [pairing_representative]
  exact (representativeForm hG model r d pi C hC mu hsq A).add_left _ _ _

theorem pairing_smul_left (c : ℂ) :
    pairing hG model r d pi C hC mu hsq (c • v) w omega =
      (starRingEnd ℂ) c * pairing hG model r d pi C hC mu hsq v w omega := by
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
    model.normCharacters pi C hC mu hsq omega
  simp only [pairing_representative]
  exact (representativeForm hG model r d pi C hC mu hsq A).smul_left _ _ _

theorem pairing_conj_symm :
    (starRingEnd ℂ) (pairing hG model r d pi C hC mu hsq w v omega) =
      pairing hG model r d pi C hC mu hsq v w omega := by
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
    model.normCharacters pi C hC mu hsq omega
  simp only [pairing_representative]
  exact (representativeForm hG model r d pi C hC mu hsq A).conj_inner_symm _ _

theorem pairing_add_right :
    pairing hG model r d pi C hC mu hsq v (w + z) omega =
      pairing hG model r d pi C hC mu hsq v w omega +
        pairing hG model r d pi C hC mu hsq v z omega := by
  have h := congrArg (starRingEnd ℂ) (pairing_add_left hG model r d pi C hC mu hsq w z v omega)
  rwa [map_add, pairing_conj_symm, pairing_conj_symm, pairing_conj_symm] at h

theorem pairing_smul_right (c : ℂ) :
    pairing hG model r d pi C hC mu hsq v (c • w) omega =
      c * pairing hG model r d pi C hC mu hsq v w omega := by
  have h := congrArg (starRingEnd ℂ) (pairing_smul_left hG model r d pi C hC mu hsq w v omega c)
  rwa [map_mul, Complex.conj_conj, pairing_conj_symm, pairing_conj_symm] at h

/-- The published actual coefficient action on this exact smooth component. -/
def smoothAction : Representation ℂ (rationalPoints G × rationalPoints G)
    (smoothOrbitSections model d pi) :=
  productInducedSmoothOrbitRepresentation (decomposition t) (isClosed_radical t)
    model.normCharacters pi d.compact (isClosed_parabolic t) d.isCompact
    model.continuous_normCharacters d.projection_continuous d.factorization
    model.unitaryCoordinates.toMulEquiv model.unitaryCoordinates_hasLaurent

/-- The actual inverse-degree pairing is invariant under the full product action. -/
theorem pairing_action (x : rationalPoints G × rationalPoints G)
    (v w : smoothOrbitSections model d pi)
    (omega : discreteSeriesOrbit C hC mu model.normCharacters (discreteSeriesClass C hC mu pi hsq)) :
    pairing hG model r d pi C hC mu hsq (smoothAction model d pi x v)
      (smoothAction model d pi x w) omega = pairing hG model r d pi C hC mu hsq v w omega :=
  unitaryOrbitProductPairing_full_action (decomposition t) (isClosed_radical t)
    model.normCharacters pi d.compact (isClosed_parabolic t) d.isCompact
    model.continuous_normCharacters d.projection_continuous d.factorization
    model.unitaryCoordinates.toMulEquiv (ambient_modularCharacter hG)
    (parabolic_modularCharacter hG model r d) (compactOpenCofinal_levi model d)
    C hC mu hsq model.unitaryCoordinates_hasLaurent x v w omega

/-- The actual density at the primitive scalar data, with no free weight. -/
def orbitDensity (q : OrbitPacketData r pi) :
    discreteSeriesOrbit C hC mu model.normCharacters (discreteSeriesClass C hC mu pi hsq) → ℂ :=
  SourceDensity.orbitPlancherelWeight model r pi C hC mu hsq q.reflection q.centralCharacters
    q.compact q.isCompact q.factorization q.oppositeFactorization q.forward q.reverse
    q.forwardOpen q.forwardNonempty q.forwardContained q.reverseOpen q.reverseNonempty
    q.reverseContained q.irreducibleOpen q.irreducibleNonempty q.irreducible q.inverseRegular

omit [BorelSpace (levi t ⧸ C)] [mu.IsInvInvariant] in
theorem continuous_orbitDensity (q : OrbitPacketData r pi) :
    Continuous (orbitDensity hG model r pi C hC mu hsq q) :=
  SourceDensity.continuous_orbitPlancherelWeight model r pi C hC mu hsq q.reflection q.centralCharacters
    q.compact q.isCompact q.factorization q.oppositeFactorization q.forward q.reverse
    q.forwardOpen q.forwardNonempty q.forwardContained q.reverseOpen q.reverseNonempty
    q.reverseContained q.irreducibleOpen q.irreducibleNonempty q.irreducible q.inverseRegular

end Pairing

section SourceNormalized

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [MeasurableSpace (levi t ⧸ model.splitCenter a)] [BorelSpace (levi t ⧸ model.splitCenter a)]
  (mu : Measure (levi t ⧸ model.splitCenter a)) [mu.IsHaarMeasure] [mu.IsInvInvariant]
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t))
  (hsq : IsSquareIntegrableModCentralSubgroup (model.splitCenter a)
    (model.splitCenter_le_center a ha) pi.obj.representation mu)
  (q : OrbitPacketData r pi)

set_option hygiene false in
local notation "C" => model.splitCenter a
set_option hygiene false in
local notation "hC" => model.splitCenter_le_center a ha
set_option hygiene false in
local notation "omega0" => discreteSeriesClass C hC mu pi hsq
set_option hygiene false in
local notation "Opi" => discreteSeriesOrbit C hC mu model.normCharacters omega0
set_option hygiene false in
local notation "eta" => SourceMeasure.normalizedOrbitMeasure model a ha hindex mu omega0
set_option hygiene false in
local notation "W" => orbitDensity hG model r pi C hC mu hsq q
set_option hygiene false in
local notation "pair" => pairing hG model r d pi C hC mu hsq

/-- Scalar integrability of the exact density-weighted inverse-degree pairing. -/
theorem integrable_pairing (v w : smoothOrbitSections model d pi) :
    Integrable (fun omega : Opi => W omega * pair v w omega) eta := by
  let := SourcePacket.sourceOrbit_compactSpace model a ha mu pi hsq
  have hcont := (continuous_orbitDensity hG model r pi C hC mu hsq q).mul
    (continuous_pairing hG model r d pi C hC mu hsq v w)
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hcont⟩).integrable eta

/-- The actual one-orbit integral in VII.2, before any global sum. -/
def weightedOrbitForm (v w : smoothOrbitSections model d pi) : ℂ :=
  ∫ omega : Opi, W omega * pair v w omega ∂eta

set_option hygiene false in
local notation "B" => weightedOrbitForm hG model r d a ha hindex mu pi hsq q

theorem weightedOrbitForm_add_left (v w z : smoothOrbitSections model d pi) :
    B (v + w) z = B v z + B w z := by
  unfold weightedOrbitForm
  rw [← integral_add
    (integrable_pairing hG model r d a ha hindex mu pi hsq q v z)
    (integrable_pairing hG model r d a ha hindex mu pi hsq q w z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  dsimp only
  rw [pairing_add_left, mul_add]

theorem weightedOrbitForm_add_right (v w z : smoothOrbitSections model d pi) :
    B v (w + z) = B v w + B v z := by
  unfold weightedOrbitForm
  rw [← integral_add
    (integrable_pairing hG model r d a ha hindex mu pi hsq q v w)
    (integrable_pairing hG model r d a ha hindex mu pi hsq q v z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  dsimp only
  rw [pairing_add_right, mul_add]

theorem weightedOrbitForm_smul_left (c : ℂ) (v w : smoothOrbitSections model d pi) :
    B (c • v) w = (starRingEnd ℂ) c * B v w := by
  unfold weightedOrbitForm
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  dsimp only
  rw [pairing_smul_left]
  ring

theorem weightedOrbitForm_smul_right (c : ℂ) (v w : smoothOrbitSections model d pi) :
    B v (c • w) = c * B v w := by
  unfold weightedOrbitForm
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  dsimp only
  rw [pairing_smul_right]
  ring

/-- The source integral inherits the actual full product-group invariance. -/
theorem weightedOrbitForm_action (x : rationalPoints G × rationalPoints G)
    (v w : smoothOrbitSections model d pi) :
    B (smoothAction model d pi x v) (smoothAction model d pi x w) = B v w := by
  unfold weightedOrbitForm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega =>
    congrArg (W omega * ·) (pairing_action hG model r d pi C hC mu hsq x v w omega)

/-- The integral itself supplies the sesquilinear map; no form is selected. -/
def orbitSesquilinear : smoothOrbitSections model d pi →ₗ⋆[ℂ]
    smoothOrbitSections model d pi →ₗ[ℂ] ℂ where
  toFun v :=
    { toFun := B v
      map_add' := weightedOrbitForm_add_right hG model r d a ha hindex mu pi hsq q v
      map_smul' := fun c w => weightedOrbitForm_smul_right hG model r d a ha hindex mu pi hsq q c v w }
  map_add' v w := LinearMap.ext fun z => weightedOrbitForm_add_left hG model r d a ha hindex mu pi hsq q v w z
  map_smul' c v := LinearMap.ext fun w => weightedOrbitForm_smul_left hG model r d a ha hindex mu pi hsq q c v w

end SourceNormalized

end SourceForm

namespace GlobalForm

variable (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure] [∀ t, (mu t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

/-- The actual source-weighted scalar integral at one full-family component. -/
def componentForm (theta : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d theta →ₗ⋆[ℂ]
      rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d theta →ₗ[ℂ] ℂ :=
  SourceForm.orbitSesquilinear hG (chosenLeviModel theta.1) (rs theta.1) (d theta.1)
    (a theta.1) (ha theta.1) (hindex theta.1) (mu theta.1)
    (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel theta.1) (a theta.1)
      (ha theta.1) (mu theta.1) theta.2) (Q theta)

/-- The global form is this actual weighted sum of source integrals,
conjugate linear in the first argument and linear in the second. -/
def rawGlobalForm : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ⋆[ℂ]
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ] ℂ :=
  FiniteSupportSections.totalSesquilinear
    (rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d)
    (fun theta => (GlobalSynthesis.sourceWeight hG rs K0 hK0 theta.1 : ℂ) •
      componentForm hG a ha mu d rs hindex Q theta)

/-- The actual scalar expression, before replacing its finite sum by a finset. -/
theorem rawGlobalForm_finsum (f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f g =
      ∑ᶠ theta, (GlobalSynthesis.sourceWeight hG rs K0 hK0 theta.1 : ℂ) *
        componentForm hG a ha mu d rs hindex Q theta
          (rationalSemistandardThetaComponent a ha mu d theta f)
          (rationalSemistandardThetaComponent a ha mu d theta g) := rfl

/-- The source sum is finite already on the second input's literal support. -/
theorem rawGlobalForm_apply (f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f g =
      ∑ theta ∈ g.property.2.toFinset,
        (GlobalSynthesis.sourceWeight hG rs K0 hK0 theta.1 : ℂ) *
          componentForm hG a ha mu d rs hindex Q theta
            (rationalSemistandardThetaComponent a ha mu d theta f)
            (rationalSemistandardThetaComponent a ha mu d theta g) := by
  have h := FiniteSupportSections.totalLinear_apply
    (rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d)
    (fun theta => ((GlobalSynthesis.sourceWeight hG rs K0 hK0 theta.1 : ℂ) •
      componentForm hG a ha mu d rs hindex Q theta)
      (rationalSemistandardThetaComponent a ha mu d theta f)) g
  simp only [LinearMap.smul_apply, smul_eq_mul] at h
  convert h using 1 <;> rfl

omit [∀ t, IsAffine (T t).X.left] [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, (mu t).IsInvInvariant] in
/-- Global component evaluation intertwines the same actual coefficient action. -/
theorem component_action (x : rationalPoints G × rationalPoints G)
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (theta : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaComponent a ha mu d theta
        (rationalSemistandardThetaSmoothRepresentation a ha mu d x f) =
      SourceForm.smoothAction (chosenLeviModel theta.1) (d theta.1)
        (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
        x (rationalSemistandardThetaComponent a ha mu d theta f) := rfl

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
/-- Actual full G x G invariance is inherited from the source inverse-degree
fiber forms, without any positivity premise on the density. -/
theorem rawGlobalForm_action (x : rationalPoints G × rationalPoints G)
    (f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    rawGlobalForm hG a ha mu d rs hindex Q K0 hK0
        (rationalSemistandardThetaSmoothRepresentation a ha mu d x f)
        (rationalSemistandardThetaSmoothRepresentation a ha mu d x g) =
      rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f g := by
  change (∑ᶠ theta, (GlobalSynthesis.sourceWeight hG rs K0 hK0 theta.1 : ℂ) *
    componentForm hG a ha mu d rs hindex Q theta
      (rationalSemistandardThetaComponent a ha mu d theta
        (rationalSemistandardThetaSmoothRepresentation a ha mu d x f))
      (rationalSemistandardThetaComponent a ha mu d theta
        (rationalSemistandardThetaSmoothRepresentation a ha mu d x g))) =
    ∑ᶠ theta, (GlobalSynthesis.sourceWeight hG rs K0 hK0 theta.1 : ℂ) *
      componentForm hG a ha mu d rs hindex Q theta
        (rationalSemistandardThetaComponent a ha mu d theta f)
        (rationalSemistandardThetaComponent a ha mu d theta g)
  apply finsum_congr
  intro theta
  rw [component_action, component_action]
  congr 1
  exact SourceForm.weightedOrbitForm_action hG (chosenLeviModel theta.1) (rs theta.1) (d theta.1)
    (a theta.1) (ha theta.1) (hindex theta.1) (mu theta.1)
    (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel theta.1) (a theta.1)
      (ha theta.1) (mu theta.1) theta.2) (Q theta) x
    (rationalSemistandardThetaComponent a ha mu d theta f)
    (rationalSemistandardThetaComponent a ha mu d theta g)

/-- The actual unitary orbit at one full-family index. -/
abbrev OrbitPoint (theta : RationalSemistandardTheta.{u, uV} a ha mu) :=
  discreteSeriesOrbit ((chosenLeviModel theta.1).splitCenter (a theta.1))
    ((chosenLeviModel theta.1).splitCenter_le_center (a theta.1) (ha theta.1))
    (mu theta.1) (chosenLeviModel theta.1).normCharacters
    (discreteSeriesClass ((chosenLeviModel theta.1).splitCenter (a theta.1))
      ((chosenLeviModel theta.1).splitCenter_le_center (a theta.1) (ha theta.1))
      (mu theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
      (orbitRepresentative_isSquareIntegrable (chosenLeviModel theta.1) (a theta.1)
        (ha theta.1) (mu theta.1) theta.2))

/-- This is the exact density used in both the source packet and the global integral. -/
def componentDensity (theta : RationalSemistandardTheta.{u, uV} a ha mu) :
    OrbitPoint a ha mu theta → ℂ :=
  SourceForm.orbitDensity hG (chosenLeviModel theta.1) (rs theta.1)
    (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
    ((chosenLeviModel theta.1).splitCenter (a theta.1))
    ((chosenLeviModel theta.1).splitCenter_le_center (a theta.1) (ha theta.1)) (mu theta.1)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel theta.1) (a theta.1)
      (ha theta.1) (mu theta.1) theta.2) (Q theta)

/-- Concrete scalar nonnegativity of the actual densities, retained as an
existing scalar/density obligation rather than a global form hypothesis. -/
def DensityNonnegative : Prop :=
  ∀ (theta : RationalSemistandardTheta.{u, uV} a ha mu) (omega : OrbitPoint a ha mu theta),
    ∃ b : ℝ, 0 ≤ b ∧ componentDensity hG a ha mu rs Q theta omega = (b : ℂ)

/-- Density positivity is required only on a dense set in each actual orbit. -/
def DensityPositiveDense : Prop :=
  ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    Dense {omega : OrbitPoint a ha mu theta | 0 < (componentDensity hG a ha mu rs Q theta omega).re}

/-- The actual integral form must be Hermitian and positive definite under
the preceding actual scalar-density and geometric-finiteness inputs. It takes
no positive form or any of its own conclusions as data. -/
def PositiveFormStatement : Prop :=
  SemistandardSpectralFiberFinitenessStatement.{u} → IsMaximalSplitTorus i →
    DensityNonnegative hG a ha mu rs Q → DensityPositiveDense hG a ha mu rs Q →
      (∀ f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d,
        (starRingEnd ℂ) (rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 g f) =
          rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f g) ∧
      (∀ f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d,
        0 ≤ (rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f f).re) ∧
      (∀ f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d,
        rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f f = 0 → f = 0)

/-- Conditional construction keeps the integral itself as the inner product.
Sesquilinearity and action invariance are already proved. -/
def invariantPositiveForm
    (h : PositiveFormStatement hG a ha mu d rs hindex Q K0 hK0)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
    (hn : DensityNonnegative hG a ha mu rs Q) (hdense : DensityPositiveDense hG a ha mu rs Q) :
    InvariantPositiveForm (rationalSemistandardThetaSmoothRepresentation a ha mu d) where
  inner f g := rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f g
  conj_inner_symm := (h hfin hi hn hdense).1
  re_inner_nonneg := (h hfin hi hn hdense).2.1
  add_left f g z := congrArg (fun L => L z)
    ((rawGlobalForm hG a ha mu d rs hindex Q K0 hK0).map_add f g)
  smul_left f g c := by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using
      congrArg (fun L => L g) ((rawGlobalForm hG a ha mu d rs hindex Q K0 hK0).map_smulₛₗ c f)
  definite := (h hfin hi hn hdense).2.2
  invariant := rawGlobalForm_action hG a ha mu d rs hindex Q K0 hK0

/-- The conditional form is precisely the actual integral, with no selected alternative. -/
theorem invariantPositiveForm_inner
    (h : PositiveFormStatement hG a ha mu d rs hindex Q K0 hK0)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
    (hn : DensityNonnegative hG a ha mu rs Q) (hdense : DensityPositiveDense hG a ha mu rs Q)
    (f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    (invariantPositiveForm hG a ha mu d rs hindex Q K0 hK0 h hfin hi hn hdense).inner f g =
      rawGlobalForm hG a ha mu d rs hindex Q K0 hK0 f g := rfl

end GlobalForm

end RationalSemistandard

end Langlands.HarishChandraSchwartz
