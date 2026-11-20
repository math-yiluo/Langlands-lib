import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonalityDense
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Representation.Plancherel.RationalCentralQuotient

/-! # Actual semistandard packet detection and Waldspurger VII.2.3 -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ p, IsAffine (T p).X.left]
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure] [∀ p, (mu p).IsInvInvariant]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Sections" => rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
set_option hygiene false in
local notation "SplitCenter" => fun p => (chosenLeviModel p).splitCenter (a p)
set_option hygiene false in
local notation "SplitCentral" => fun p => (chosenLeviModel p).splitCenter_le_center (a p) (ha p)

variable (Q : ∀ theta : Theta, OrbitPacketData (rs theta.1)
  (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2))

set_option hygiene false in
local notation "Packet" => GlobalSynthesis.componentPacket hG a ha mu d rs hindex Q
set_option hygiene false in
local notation "Density" => GlobalForm.componentDensity hG a ha mu rs Q
set_option hygiene false in
local notation "Form" => GlobalForm.componentForm hG a ha mu d rs hindex Q

local instance parabolicLocallyCompact (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace

include ha hindex in
omit [LocallyOfFiniteType G.X.hom] [∀ p, IsAffine (T p).X.left]
  [∀ p, MeasurableSpace (levi p ⧸ SplitCenter p)]
  [∀ p, BorelSpace (levi p ⧸ SplitCenter p)] in
/-- The source split valuation index gives the quotient finiteness on the literal Levi. -/
private theorem finite_componentNormKernelQuotient (p : SemistandardSpectralIndex i) :
    Finite (levi p ⧸ (commonNormKernel (chosenLeviModel p).normCharacters ⊔ SplitCenter p)) := by
  let m := chosenLeviModel p
  have := m.reductive.isAffineHom
  have : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
  let : TopologicalSpace (rationalPoints m.scheme) := rationalPointTopology F m.scheme.X
  let e := m.pointHomeomorph.toMulEquiv
  let := finite_rationalCentralQuotient (a p) (ha p).isCentralSplitTorus.isCentral (hindex p)
  have hker : (rationalCommonNormKernel m.scheme).map e.toMonoidHom =
      commonNormKernel m.normCharacters := by
    rw [Subgroup.map_equiv_eq_comap_symm' e]
    ext x
    simp only [LeviModel.normCharacters, rationalCommonNormKernel, mem_commonNormKernel,
      Subgroup.mem_comap, MonoidHom.comp_apply]
    rfl
  have hmap :
      (rationalCommonNormKernel m.scheme ⊔ (rationalPoints.map (a p)).range).map e.toMonoidHom =
        commonNormKernel m.normCharacters ⊔ SplitCenter p := by
    rw [Subgroup.map_sup, hker]
    rfl
  exact Finite.of_injective _ (QuotientGroup.congr _ _ e hmap).symm.injective

section OneOrbitForm

variable (theta : Theta)

set_option hygiene false in
local notation "p" => theta.1
set_option hygiene false in
local notation "m" => chosenLeviModel theta.1
set_option hygiene false in
local notation "C" => SplitCenter theta.1
set_option hygiene false in
local notation "hC" => SplitCentral theta.1
set_option hygiene false in
local notation "pi" => orbitRepresentative m (a p) (ha p) (mu p) theta.2
set_option hygiene false in
local notation "hsq" => orbitRepresentative_isSquareIntegrable m (a p) (ha p) (mu p) theta.2
set_option hygiene false in
local notation "omega0" => discreteSeriesClass C hC (mu p) pi hsq
set_option hygiene false in
local notation "Orbit" => GlobalForm.OrbitPoint a ha mu theta
set_option hygiene false in
local notation "eta" => SourceMeasure.normalizedOrbitMeasure m (a p) (ha p) (hindex p) (mu p) omega0
set_option hygiene false in
local notation "E" => SourcePacket.coefficientMap hG m (rs p) (d p) pi C hC (mu p) hsq
set_option hygiene false in
local notation "B" => SourceForm.pairing hG m (rs p) (d p) pi C hC (mu p) hsq

omit [∀ p0, IsAffine (T p0).X.left]
  [∀ p0, (rationalPoints.map (a p0)).range.Normal]
  [∀ p0, BorelSpace (levi p0 ⧸ SplitCenter p0)] [∀ p0, (mu p0).IsInvInvariant] in
/-- The real representative of the actual density under its V.2 nonnegativity condition. -/
private theorem density_eq_ofReal_re
    (hn : GlobalForm.DensityNonnegative hG a ha mu rs Q) (omega : Orbit) :
    ((Density theta omega).re : ℂ) = Density theta omega := by
  obtain ⟨c, _, hc⟩ := hn theta omega
  rw [hc, Complex.ofReal_re]

/-- Definiteness of the actual source-normalized component form. -/
theorem componentForm_self_eq_zero_iff
    (hn : GlobalForm.DensityNonnegative hG a ha mu rs Q)
    (hdense : GlobalForm.DensityPositiveDense hG a ha mu rs Q) (v : Sections theta) :
    Form theta v v = 0 ↔ v = 0 := by
  let := finite_componentNormKernelQuotient a ha hindex p
  let : CompactSpace Orbit := SourcePacket.sourceOrbit_compactSpace m (a p) (ha p) (mu p) pi hsq
  let := SourceMeasure.finite_literalDiscreteSeriesStabilizer m (a p) (ha p) (hindex p) (mu p) omega0
  let u : Orbit → ℝ := fun omega => (Density theta omega).re
  have hu : Continuous u := Complex.continuous_re.comp
    (SourceForm.continuous_orbitDensity hG m (rs p) pi C hC (mu p) hsq (Q theta))
  have hu0 (omega : Orbit) : 0 ≤ u omega := by
    obtain ⟨c, hc, heq⟩ := hn theta omega
    simpa only [u, heq, Complex.ofReal_re] using hc
  obtain ⟨b, hb⟩ := (isCompact_univ.image hu).bddAbove
  have hub (omega : Orbit) : u omega ≤ b := hb (Set.mem_image_of_mem u (Set.mem_univ omega))
  have hre : (fun omega : Orbit => (u omega : ℂ)) = Density theta :=
    funext (density_eq_ofReal_re hG a ha mu rs Q theta hn)
  change (∫ omega : Orbit, Density theta omega * B v v omega ∂eta) = 0 ↔ v = 0
  rw [← hre, SourceMeasure.normalizedOrbitMeasure_eq]
  exact unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense
    (decomposition p) (isClosed_radical p) (isClosed_parabolic p)
    (d p).compact (d p).isCompact (d p).factorization (ambient_modularCharacter hG)
    (parabolic_modularCharacter hG m (rs p) (d p)) (m).normCharacters pi (m).continuous_normCharacters
    (d p).projection_continuous (m).unitaryCoordinates.toMulEquiv (compactOpenCofinal_levi m (d p))
    C hC (mu p) hsq (SourceMeasure.unitaryCharacterHaar m (a p) (ha p) (hindex p)) u
    (m).unitaryCoordinates.continuous hu hu0 (hdense theta) hub v

end OneOrbitForm

variable {nu : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "Schwartz" => RationalSchwartzSpace hK hPK rho
set_option hygiene false in
local notation "dg" => RationalDynamicSource.ambientHaar K hK

include hG in
private theorem sourceHaarRightInvariant : (dg).IsMulRightInvariant :=
  Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one (ambient_modularCharacter hG) dg

variable (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  (hsw : SquareIntegrableWeight dg (rationalXi hK hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup (SplitCenter p) (SplitCentral p) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
local notation "Fourier" => (
  letI := sourceHaarRightInvariant hG hK
  rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT)

section FourierPairing

variable (theta : Theta)

set_option hygiene false in
local notation "p" => theta.1
set_option hygiene false in
local notation "m" => chosenLeviModel theta.1
set_option hygiene false in
local notation "C" => SplitCenter theta.1
set_option hygiene false in
local notation "hC" => SplitCentral theta.1
set_option hygiene false in
local notation "pi" => orbitRepresentative m (a p) (ha p) (mu p) theta.2
set_option hygiene false in
local notation "hsq" => orbitRepresentative_isSquareIntegrable m (a p) (ha p) (mu p) theta.2
set_option hygiene false in
local notation "omega0" => discreteSeriesClass C hC (mu p) pi hsq
set_option hygiene false in
local notation "Orbit" => GlobalForm.OrbitPoint a ha mu theta
set_option hygiene false in
local notation "eta" => SourceMeasure.normalizedOrbitMeasure m (a p) (ha p) (hindex p) (mu p) omega0
set_option hygiene false in
local notation "E" => SourcePacket.coefficientMap hG m (rs p) (d p) pi C hC (mu p) hsq
set_option hygiene false in
local notation "B" => SourceForm.pairing hG m (rs p) (d p) pi C hC (mu p) hsq

/-- The VI.2.2 double integrability needed for pairing a packet with a Schwartz function. -/
def OrbitProductIntegrabilityStatement : Prop :=
  ∀ (v : Sections theta) (f : Schwartz),
    Integrable
      (fun x : rationalPoints G × Orbit => conj (Density theta x.2 * E v x.2 x.1) * f x.1)
      ((dg).prod eta)

omit [∀ p0, IsAffine (T p0).X.left] [∀ p0, (rationalPoints.map (a p0)).range.Normal] in
/-- VII.1.1(ii) at each actual orbit point, using coherent representative descent. -/
theorem orbitCoefficient_pairing (v : Sections theta) (f : Schwartz)
    (hsm : Fourier f theta ∈ Sections theta) (omega : Orbit) :
    (∫ g, conj (E v omega g) * f g ∂dg) = B v ⟨Fourier f theta, hsm⟩ omega := by
  let := sourceHaarRightInvariant hG hK
  let := Langlands.isInvInvariant_of_isMulRightInvariant dg
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
    (m).normCharacters pi C hC (mu p) hsq omega
  let v₀ : smoothOrbitSections m (d p) pi := v
  let w₀ : smoothOrbitSections m (d p) pi := ⟨Fourier f theta, hsm⟩
  let ω := unitaryOrbitRepresentativeDiscreteSeriesOrbit (m).normCharacters pi C hC (mu p) hsq A
  change (∫ g, conj (E v₀ ω g) * f g ∂dg) = B v₀ w₀ ω
  rw [SourcePacket.coefficientMap_representative hG m (rs p) (d p) pi C hC (mu p) hsq v₀ A,
    SourceForm.pairing_representative hG m (rs p) (d p) pi C hC (mu p) hsq v₀ w₀ A]
  have hA := unitaryOrbitRepresentative_isDiscreteSeries (m).normCharacters pi C hC (mu p) hsq A
  exact rationalSemistandardFourier_pairing (mu := dg) hG hi hnu hK hPK rho hsw
    p (d p) (hdelta p) A.val.obj C hC (mu p) hA A.val.property.1 (hT p A.val hA) (v₀.val A) f

/-- Formula (1) in the proof of VII.2.2, for the actual full Fourier component. -/
theorem packet_pairing_eq_componentForm
    (hn : GlobalForm.DensityNonnegative hG a ha mu rs Q)
    (hint : OrbitProductIntegrabilityStatement hG a ha mu d rs hindex Q hK hPK rho theta)
    (v : Sections theta) (f : Schwartz) (hsm : Fourier f theta ∈ Sections theta) :
    HarishChandraSchwartz.pairing dg (Packet theta v) f = Form theta v ⟨Fourier f theta, hsm⟩ := by
  change (∫ g, conj (∫ omega : Orbit, Density theta omega * E v omega g ∂eta) * f g ∂dg) =
    ∫ omega : Orbit, Density theta omega * B v ⟨Fourier f theta, hsm⟩ omega ∂eta
  calc
    _ = ∫ g, ∫ omega : Orbit, conj (Density theta omega * E v omega g) * f g ∂eta ∂dg := by
      simp_rw [integral_mul_const, integral_conj]
    _ = ∫ omega : Orbit, ∫ g, conj (Density theta omega * E v omega g) * f g ∂dg ∂eta :=
      integral_integral_swap (hint v f)
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      change (∫ g, conj (Density theta omega * E v omega g) * f g ∂dg) =
        Density theta omega * B v ⟨Fourier f theta, hsm⟩ omega
      calc
        _ = Density theta omega * ∫ g, conj (E v omega g) * f g ∂dg := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          have hconj : conj (Density theta omega) = Density theta omega := by
            rw [← density_eq_ofReal_re hG a ha mu rs Q theta hn omega, Complex.conj_ofReal]
          simp only [map_mul, hconj, mul_assoc]
        _ = _ := congrArg (fun z => Density theta omega * z)
          (orbitCoefficient_pairing hG a ha mu d rs hK hPK rho hi hnu hsw hdelta hT
            theta v f hsm omega)

/-- The actual semistandard Fourier component is detected by all smooth source packets. -/
theorem component_eq_zero_iff_forall_pairing_eq_zero
    (hn : GlobalForm.DensityNonnegative hG a ha mu rs Q)
    (hdense : GlobalForm.DensityPositiveDense hG a ha mu rs Q)
    (hint : OrbitProductIntegrabilityStatement hG a ha mu d rs hindex Q hK hPK rho theta)
    (f : Schwartz) (hsm : Fourier f theta ∈ Sections theta) :
    Fourier f theta = 0 ↔
      ∀ v : Sections theta, HarishChandraSchwartz.pairing dg (Packet theta v) f = 0 := by
  let w : Sections theta := ⟨Fourier f theta, hsm⟩
  constructor
  · intro h v
    rw [packet_pairing_eq_componentForm hG a ha mu d rs hindex Q hK hPK rho hi hnu hsw hdelta hT
      theta hn hint v f hsm]
    exact (congrArg (Form theta v) (Subtype.ext h : w = 0)).trans (map_zero _)
  · intro h
    have hw : Form theta w w = 0 :=
      (packet_pairing_eq_componentForm hG a ha mu d rs hindex Q hK hPK rho hi hnu hsw hdelta hT
        theta hn hint w f hsm).symm.trans (h w)
    exact congrArg Subtype.val ((componentForm_self_eq_zero_iff hG a ha mu d rs hindex Q theta
      hn hdense w).mp hw)

end FourierPairing

section Pointwise

/-- The actual VII.1 Fourier tensor at a specified inducing object. -/
abbrev fourierAt (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup (SplitCenter p) (SplitCentral p)
      A.obj.representation (mu p)) :
    Schwartz →ₗ[ℂ] productInducedCoefficientObject (decomposition p) (isClosed_radical p) A.obj :=
  letI := sourceHaarRightInvariant hG hK
  rationalSemistandardInducedFourierTransform hG hi hnu hK hPK rho hsw
    p (d p) (hdelta p) A.obj (SplitCenter p) (SplitCentral p) (mu p) hsq A.property.1 (hT p A hsq)

set_option hygiene false in
local notation "At" => fourierAt hG a ha mu d hK hPK rho hi hnu hsw hdelta hT

omit [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal] in
/-- Evaluation at an inducing representative of the chosen full-product component. -/
theorem fourierComponent_apply (f : Schwartz) (theta : Theta)
    (A : UnitaryOrbitRepresentative (chosenLeviModel theta.1).normCharacters
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)) :
    Fourier f theta A = At theta.1 A.val (unitaryOrbitRepresentative_isDiscreteSeries _ _ _ _ _
      (orbitRepresentative_isSquareIntegrable
        (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2) A) f := rfl

set_option maxHeartbeats 4800000 in
omit [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal] in
/-- The product and pointwise formulations agree by actual orbit membership and evaluation. -/
theorem fourierComponents_eq_zero_iff_forall_fourierAt_eq_zero
    (f : Schwartz) (p : SemistandardSpectralIndex i) :
    (∀ O : OrbitClass (chosenLeviModel p) (a p) (ha p) (mu p), Fourier f ⟨p, O⟩ = 0) ↔
      ∀ (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
        (hsq : IsSquareIntegrableModCentralSubgroup (SplitCenter p) (SplitCentral p)
          A.obj.representation (mu p)), At p A hsq f = 0 := by
  constructor
  · intro h A hsq
    let O : OrbitClass (chosenLeviModel p) (a p) (ha p) (mu p) :=
      Quotient.mk _ (discreteSeriesClass (SplitCenter p) (SplitCentral p) (mu p) A hsq)
    let A' := orbitRepresentativeMember (chosenLeviModel p) (a p) (ha p) (mu p) O A hsq rfl
    have hzero := congrArg (fun w : RationalSemistandardThetaSection a ha mu ⟨p, O⟩ => w A') (h O)
    have heval := fourierComponent_apply hG a ha mu d hK hPK rho hi hnu hsw hdelta hT f ⟨p, O⟩ A'
    change Fourier f ⟨p, O⟩ A' = At p A hsq f at heval
    exact heval.symm.trans hzero
  · intro h O
    apply funext
    intro A
    change Fourier f ⟨p, O⟩ A = (0 : productInducedCoefficientObject (decomposition p)
      (isClosed_radical p) A.val.obj)
    rw [fourierComponent_apply hG a ha mu d hK hPK rho hi hnu hsw hdelta hT f ⟨p, O⟩ A]
    apply h

variable (hmem : ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho)

set_option hygiene false in
local notation "fPacket" => schwartzPacket hG a ha mu d rs hindex Q hK hPK rho hmem
set_option hygiene false in
local notation "SourceCompact" => SourceCompactCompatibility hG a ha mu d rs Q (nu := nu) (K := K)

/-- Waldspurger VII.2.3 in the literal target coefficient fiber at each discrete series. -/
def PointwiseVanishingStatement : Prop :=
  SourceCompact →
  ∀ (theta : Theta) (v : Sections theta) (p' : SemistandardSpectralIndex i),
    ¬ LevisConjugate theta.1 p' →
      ∀ (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p'))
        (hsq : IsSquareIntegrableModCentralSubgroup (SplitCenter p') (SplitCentral p')
          A.obj.representation (mu p')), At p' A hsq (fPacket theta v) = 0

/-- The same target in the actual full Fourier product. -/
def ComponentVanishingStatement : Prop :=
  SourceCompact →
  ∀ (theta : Theta) (v : Sections theta) (theta' : Theta),
    ¬ LevisConjugate theta.1 theta'.1 → Fourier (fPacket theta v) theta' = 0

/-- Equivalence of the two VII.2.3 targets. -/
theorem pointwiseVanishing_iff_componentVanishing :
    PointwiseVanishingStatement hG a ha mu d rs hindex Q hK hPK rho hi hnu hsw hdelta hT hmem ↔
      ComponentVanishingStatement hG a ha mu d rs hindex Q hK hPK rho hi hnu hsw hdelta hT hmem := by
  constructor
  · intro h hsource theta v theta' hnon
    exact ((fourierComponents_eq_zero_iff_forall_fourierAt_eq_zero hG a ha mu d hK hPK rho
      hi hnu hsw hdelta hT (fPacket theta v) theta'.1).mpr (h hsource theta v theta'.1 hnon)) theta'.2
  · intro h hsource theta v p' hnon
    exact (fourierComponents_eq_zero_iff_forall_fourierAt_eq_zero hG a ha mu d hK hPK rho
      hi hnu hsw hdelta hT (fPacket theta v) p').mp (fun O => h hsource theta v ⟨p', O⟩ hnon)

/-- VII.2.2(i) implies VII.2.3 under the preceding actual Fourier and Fubini conditions. -/
theorem componentVanishing_of_nonconjugatePairing
    (hn : GlobalForm.DensityNonnegative hG a ha mu rs Q)
    (hdense : GlobalForm.DensityPositiveDense hG a ha mu rs Q)
    (hint : ∀ theta : Theta, OrbitProductIntegrabilityStatement hG a ha mu d rs hindex Q hK hPK rho theta)
    (hsm : ∀ (f : Schwartz) (theta : Theta), Fourier f theta ∈ Sections theta)
    (hpair : NonconjugatePairingStatement hG a ha mu d rs hindex Q hK hPK rho) :
    ComponentVanishingStatement hG a ha mu d rs hindex Q hK hPK rho hi hnu hsw hdelta hT hmem := by
  intro hsource theta v theta' hnon
  apply (component_eq_zero_iff_forall_pairing_eq_zero hG a ha mu d rs hindex Q hK hPK rho
    hi hnu hsw hdelta hT theta' hn hdense (hint theta') (fPacket theta v) (hsm _ _)).mpr
  intro v'
  exact hpair hi hnu hsource hmem theta theta' hnon v v'

end Pointwise

end Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing
