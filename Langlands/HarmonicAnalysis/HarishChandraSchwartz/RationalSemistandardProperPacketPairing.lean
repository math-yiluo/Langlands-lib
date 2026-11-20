import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaParts

/-! # The VII.2 packet comparison for the convolution tests in VIII.2.3 -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance packetPairingCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance packetPairingParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {nu : cocharacterLattice S} (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "C" => RationalSchwartzSpace hKc hPK rho

set_option hygiene false in
local notation "checkSchwartz" =>
  Space.check (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)

set_option hygiene false in
local notation "translateSchwartz" =>
  Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho)

/-- The test `h ↦ conj (f (g * h⁻¹))` for convolution with the packet on the right. -/
def properPacketRightTest (f : C) (g : rationalPoints G) : C :=
  Space.complexConj (translateSchwartz g⁻¹ 1 (checkSchwartz f))

/-- The test `h ↦ conj (f (h⁻¹ * g))` for convolution with the packet on the left. -/
def properPacketLeftTest (f : C) (g : rationalPoints G) : C :=
  Space.complexConj (translateSchwartz 1 g (checkSchwartz f))

@[simp] theorem properPacketRightTest_apply (f : C) (g h : rationalPoints G) :
    properPacketRightTest hG hi hnu hKc hPK rho f g h = conj (f (g * h⁻¹)) := by
  simp [properPacketRightTest, Space.complexConj_apply, Space.translate_apply, mul_inv_rev]

@[simp] theorem properPacketLeftTest_apply (f : C) (g h : rationalPoints G) :
    properPacketLeftTest hG hi hnu hKc hPK rho f g h = conj (f (h⁻¹ * g)) := by
  simp [properPacketLeftTest, Space.complexConj_apply, Space.translate_apply, mul_inv_rev]

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ t, IsAffine (T t).X.left]
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, (rationalPoints.map (a t)).range.Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  [∀ t, BorelSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (muM : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (muM t).IsHaarMeasure] [∀ t, (muM t).IsInvInvariant]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ t : RationalSemistandardTheta.{u, uV} a ha muM,
    OrbitPacketData (rs t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2))

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha muM
set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponentSpace.{u, uV} a ha muM d
set_option hygiene false in
local notation "model(" t ")" => chosenLeviModel (t : Theta).1
set_option hygiene false in
local notation "center(" t ")" => (model(t)).splitCenter (a (t : Theta).1)
set_option hygiene false in
local notation "central(" t ")" => (model(t)).splitCenter_le_center (a (t : Theta).1) (ha t.1)
set_option hygiene false in
local notation "rep(" t ")" =>
  orbitRepresentative (model(t)) (a (t : Theta).1) (ha t.1) (muM t.1) t.2
set_option hygiene false in
local notation "sq(" t ")" =>
  orbitRepresentative_isSquareIntegrable (model(t)) (a (t : Theta).1) (ha t.1) (muM t.1) t.2
set_option hygiene false in
local notation "orbitMeasure(" t ")" =>
  SourceMeasure.normalizedOrbitMeasure (model(t)) (a (t : Theta).1) (ha t.1) (hindex t.1)
    (muM t.1) (discreteSeriesClass (center(t)) (central(t)) (muM t.1) (rep(t)) (sq(t)))
set_option hygiene false in
local notation "coefficient(" t ")" =>
  SourcePacket.coefficientMap hG (model(t)) (rs (t : Theta).1) (d t.1) (rep(t))
    (center(t)) (central(t)) (muM t.1) (sq(t))
set_option hygiene false in
local notation "orbitPairing(" t ")" =>
  SourceForm.pairing hG (model(t)) (rs (t : Theta).1) (d t.1) (rep(t))
    (center(t)) (central(t)) (muM t.1) (sq(t))
set_option hygiene false in
local notation "density" => GlobalForm.componentDensity hG a ha muM rs Q
set_option hygiene false in
local notation "packet" => componentPacket hG a ha muM d rs hindex Q
set_option hygiene false in
local notation "form" => GlobalForm.componentForm hG a ha muM d rs hindex Q
set_option hygiene false in
local notation "testRight" => properPacketRightTest hG hi hnu hKc hPK rho
set_option hygiene false in
local notation "testLeft" => properPacketLeftTest hG hi hnu hKc hPK rho

/-- The VI.2.2 product integrability used to apply Fubini in both
convolutions on each actual proper semistandard component. -/
def ProperPacketConvolutionIntegrabilityStatement (muG : Measure (rationalPoints G)) : Prop :=
  ∀ f : C, f ∈ rationalCuspidalSubmodule hKc hPK rho →
    ∀ (t : Theta), t.1.IsProper → ∀ (v : component t) (g : rationalPoints G),
      Integrable (fun x : rationalPoints G × GlobalForm.OrbitPoint a ha muM t =>
        conj (testRight f g x.1) * (density t x.2 * coefficient(t) v x.2 x.1))
        (muG.prod (orbitMeasure(t))) ∧
      Integrable (fun x : rationalPoints G × GlobalForm.OrbitPoint a ha muM t =>
        conj (testLeft f g x.1) * (density t x.2 * coefficient(t) v x.2 x.1))
        (muG.prod (orbitMeasure(t)))

variable {muG : Measure (rationalPoints G)} [muG.IsHaarMeasure] [muG.IsMulRightInvariant]
  [muG.IsInvInvariant] [SFinite muG]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (muM p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
local notation "fourier" =>
  rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT

variable (hsm : ∀ (f : C) (t : Theta), fourier f t ∈ component t)

set_option hygiene false in
local notation "smoothFourier" =>
  rationalSemistandardFourierSmoothFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT hsm

set_option hygiene false in
local notation "pairingIntegrability" =>
  ProperPacketConvolutionIntegrabilityStatement hG hi hnu hKc hPK rho a ha muM d rs hindex Q muG

private theorem componentPacket_pairing (t : Theta) (v : component t) (f : C)
    (hint : Integrable (fun x : rationalPoints G × GlobalForm.OrbitPoint a ha muM t =>
      conj (f x.1) * (density t x.2 * coefficient(t) v x.2 x.1)) (muG.prod (orbitMeasure(t)))) :
    pairing muG f (packet t v) = form t (smoothFourier f t) v := by
  have hpoint (omega : GlobalForm.OrbitPoint a ha muM t) :
      pairing muG (coefficient(t) v omega) f = orbitPairing(t) v (smoothFourier f t) omega := by
    obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
      (model(t)).normCharacters (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) omega
    erw [SourcePacket.coefficientMap_representative hG (model(t)) (rs t.1) (d t.1)
      (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) v A,
      SourceForm.pairing_representative hG (model(t)) (rs t.1) (d t.1)
        (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) v (smoothFourier f t) A]
    have hsqA := unitaryOrbitRepresentative_isDiscreteSeries
      (model(t)).normCharacters (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) A
    exact rationalSemistandardFourier_pairing hG hi hnu hKc hPK rho hsw t.1 (d t.1) (hdelta t.1)
      A.val.obj (center(t)) (central(t)) (muM t.1) hsqA A.val.property.1 (hT t.1 A.val hsqA)
      (v.val A) f
  change (∫ g, conj (f g) * (∫ omega, density t omega * coefficient(t) v omega g
    ∂orbitMeasure(t)) ∂muG) =
    ∫ omega, density t omega * orbitPairing(t) (smoothFourier f t) v omega ∂orbitMeasure(t)
  have hmul : ∀ g, conj (f g) * (∫ omega, density t omega * coefficient(t) v omega g
      ∂orbitMeasure(t)) =
      ∫ omega, conj (f g) * (density t omega * coefficient(t) v omega g) ∂orbitMeasure(t) :=
    fun g => (integral_const_mul _ _).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hmul), integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  calc
    (∫ g, conj (f g) * (density t omega * coefficient(t) v omega g) ∂muG) =
        density t omega * pairing muG f (coefficient(t) v omega) := by
      rw [pairing, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
        (mul_left_comm (conj (f g)) (density t omega) _))
    _ = density t omega * orbitPairing(t) (smoothFourier f t) v omega := by
      rw [pairing_conj_symm, hpoint]
      exact congrArg (density t omega * ·)
        (SourceForm.pairing_conj_symm hG (model(t)) (rs t.1) (d t.1)
          (rep(t)) (center(t)) (central(t)) (muM t.1) (sq(t)) (smoothFourier f t) v omega)

/-- Formula VII.2(1) in the conjugate-first order required by both
convolution tests in VIII.2.3. The component Fourier lift uses VII.1.3. -/
def ProperPacketConvolutionPairingStatement : Prop :=
  pairingIntegrability → ∀ f : C, f ∈ rationalCuspidalSubmodule hKc hPK rho →
    ∀ (t : Theta), t.1.IsProper → ∀ (v : component t) (g : rationalPoints G),
      convolution muG f (packet t v) g = form t (smoothFourier (testRight f g) t) v ∧
      convolution muG (packet t v) f g = form t (smoothFourier (testLeft f g) t) v

set_option maxHeartbeats 2000000 in
theorem properPacketConvolutionPairing :
    ProperPacketConvolutionPairingStatement hG hi hnu hKc hPK rho a ha muM d rs hindex Q
      hsw hdelta hT hsm := by
  intro hint f hf t ht v g
  obtain ⟨hRight, hLeft⟩ := hint f hf t ht v g
  have hRightTest : (testRight f g : rationalPoints G → ℂ) = fun x => conj (f (g * x⁻¹)) :=
    funext (properPacketRightTest_apply hG hi hnu hKc hPK rho f g)
  have hLeftTest : (testLeft f g : rationalPoints G → ℂ) = fun x => conj (f (x⁻¹ * g)) :=
    funext (properPacketLeftTest_apply hG hi hnu hKc hPK rho f g)
  constructor
  · rw [convolution_eq_conj_pairing muG f (packet t v) g, ← hRightTest,
      ← pairing_conj_symm muG (packet t v) (testRight f g)]
    exact componentPacket_pairing hG hi hnu hKc hPK rho a ha muM d rs hindex Q hsw hdelta hT hsm
      t v (testRight f g) hRight
  · rw [convolution_eq_conj_pairing_right muG (packet t v) f g, ← hLeftTest,
      ← pairing_conj_symm muG (packet t v) (testLeft f g)]
    exact componentPacket_pairing hG hi hnu hKc hPK rho a ha muM d rs hindex Q hsw hdelta hT hsm
      t v (testLeft f g) hLeft

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis
