import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketFourier

/-! # Waldspurger VII.2.5: the Fourier family inverts the actual synthesis on its image

The second assertion of Theorem VII.2.5 of Waldspurger (2003): for every
invariant finite-support smooth family `ψ` and every full index `(O, P)`, the
actual Fourier family of `κ(ψ)` has component `ψ_{κ(ψ)}[O, P] = ψ[O, P]`. The
target is stated pointwise at every actual inducing representative of every
orbit; this module proves its equivalence with equality in the full dependent
product and with equality after every representative change, and derives the
elementary consequences on the image of `κ`. -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact (SpecialCompactProperties)
open Langlands.Plancherel.WaldspurgerSourceNormalization (IsSourceCompactAt)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SynthesisInverse

open GlobalSynthesis GlobalForm

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

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
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (C.presentation theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  {nu : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

include hG in
/-- The source Haar measure is right invariant, by unimodularity of `G`. -/
theorem sourceHaar_isMulRightInvariant :
    (RationalDynamicSource.ambientHaar K hK).IsMulRightInvariant :=
  Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one (ambient_modularCharacter hG)
    (RationalDynamicSource.ambientHaar K hK)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Invariant" => rationalSemistandardThetaInvariantSections C
set_option hygiene false in
set_option quotPrecheck false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Schwartz" => RationalSchwartzSpace hK hPK rho
set_option hygiene false in
local notation "kappa" => invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
  hK hPK rho hmem hnu hspecial hd hQ
set_option hygiene false in
local notation "Fourier" => (
  letI := sourceHaar_isMulRightInvariant hG hK
  rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT)
set_option hygiene false in
local notation "base" t:max =>
  orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2

/-- Waldspurger VII.2.5, second assertion: for every invariant finite-support
smooth family `ψ`, every full semistandard index `t = (P, O)` and every actual
inducing representative `A` of the orbit `O`, the actual Fourier tensor of
`κ(ψ)` at `A` is the value of `ψ` at `A`. The premises are the preceding inputs
that define `κ` and the actual Fourier family (maximal split torus, geometric
fiber finiteness, generic cocharacter, special compact, common compact, VI.3.1
Schwartz membership, the `L²` weight condition, the modular normalization and
tempered coefficients of the induced representations), the source compact and
quotient Haar normalizations, and nonnegativity and dense positivity of the
actual density. -/
def SynthesisInverseStatement : Prop :=
  ∀ (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (hnu : IsGenericCocharacter i nu)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
    (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    DensityNonnegative hG a ha mu C.presentation Q →
    DensityPositiveDense hG a ha mu C.presentation Q →
    ∀ (psi : rationalSemistandardThetaInvariantSections C)
      (t : RationalSemistandardTheta.{u, uV} a ha mu)
      (A : UnitaryOrbitRepresentative (chosenLeviModel t.1).normCharacters
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)),
      (letI := sourceHaar_isMulRightInvariant hG hK;
        rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT
          (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
            hK hPK rho hmem hnu hspecial hd hQ psi)) t A =
        psi.val.val t A

/-- The same target as an equality in the actual full dependent product: the
Fourier family of `κ(ψ)` is `ψ`, regarded in the product by the inclusion of the
invariant carrier. -/
def SynthesisInverseProductStatement : Prop :=
  ∀ (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (hnu : IsGenericCocharacter i nu)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
    (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    DensityNonnegative hG a ha mu C.presentation Q →
    DensityPositiveDense hG a ha mu C.presentation Q →
    ∀ psi : rationalSemistandardThetaInvariantSections C,
      (letI := sourceHaar_isMulRightInvariant hG hK;
        rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT
          (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
            hK hPK rho hmem hnu hspecial hd hQ psi)) =
        rationalSemistandardThetaInvariantInclusion C psi

/-- The same target after every representative change: at every actual
square-integrable representative `π'` of every orbit `O`, the raw Fourier orbit
section of `κ(ψ)` based at `π'` is the base change of `ψ[O, P]` to `π'`. -/
def SynthesisInverseTransportStatement : Prop :=
  ∀ (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (hnu : IsGenericCocharacter i nu)
    (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
    (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) rho))
    (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
    (hT : ∀ (p : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
        ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
      HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
        ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation),
    IsSourceCompactAt i K.toSubgroup →
    (∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p) →
    DensityNonnegative hG a ha mu C.presentation Q →
    DensityPositiveDense hG a ha mu C.presentation Q →
    ∀ (psi : rationalSemistandardThetaInvariantSections C)
      (t : RationalSemistandardTheta.{u, uV} a ha mu)
      (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t.1))
      (hsq' : IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) pi'.obj.representation (mu t.1))
      (hO : (Quotient.mk _ (discreteSeriesClass ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1) pi' hsq') :
        OrbitClass (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1)) = t.2),
      (letI := sourceHaar_isMulRightInvariant hG hK;
        rationalSemistandardFourierOrbit hG hi hnu hK hPK rho hsw
          t.1 (chosenLeviModel t.1) (d t.1) (hdelta t.1) pi'
          ((chosenLeviModel t.1).splitCenter (a t.1))
          ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1) hsq'
          (fun A => hT t.1 A.val (unitaryOrbitRepresentative_isDiscreteSeries _ pi' _ _ _ hsq' A))
          (invariantSynthesis hG a ha mu d C.presentation hindex Q K hK C hi hfin
            hK hPK rho hmem hnu hspecial hd hQ psi)) =
        orbitSectionsBaseEquiv (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2 pi' hsq' hO
          (psi.val.val t)

/-- The pointwise and product formulations are equivalent. -/
theorem synthesisInverse_iff_product :
    SynthesisInverseStatement hG a ha mu d hindex C Q hK hPK rho ↔
      SynthesisInverseProductStatement hG a ha mu d hindex C Q hK hPK rho := by
  constructor
  · intro h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi
    funext t A
    exact h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi t A
  · intro h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi t A
    exact congrFun (congrFun (h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn
      hdense psi) t) A

/-- The pointwise formulation is equivalent to equality after every
representative change of every component. -/
theorem synthesisInverse_iff_transport :
    SynthesisInverseStatement hG a ha mu d hindex C Q hK hPK rho ↔
      SynthesisInverseTransportStatement hG a ha mu d hindex C Q hK hPK rho := by
  constructor
  · intro h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi t pi' hsq' hO
    have hcomp : Fourier (kappa psi) t = psi.val.val t := funext fun A =>
      h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi t A
    let := sourceHaar_isMulRightInvariant hG hK
    exact (rationalSemistandardFourierFamily_baseChange hG hi hnu hK hPK rho hsw a ha mu d hdelta hT
      t pi' hsq' hO (kappa psi)).symm.trans
        (congrArg (orbitSectionsBaseEquiv (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2 pi'
          hsq' hO) hcomp)
  · intro h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi t A
    let hsq := orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1)
      (mu t.1) t.2
    let hO := mk_discreteSeriesClass_orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1)
      (mu t.1) t.2
    let E := orbitSectionsBaseEquiv (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2
      (base t) hsq hO
    let := sourceHaar_isMulRightInvariant hG hK
    have hE : E (Fourier (kappa psi) t) = E (psi.val.val t) :=
      (rationalSemistandardFourierFamily_baseChange hG hi hnu hK hPK rho hsw a ha mu d hdelta hT
        t (base t) hsq hO (kappa psi)).trans
          (h hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense psi t
            (base t) hsq hO)
    exact congrFun (E.injective hE) A

section Consequences

variable (hi : IsMaximalSplitTorus i) (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
  (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
  (hd : ∀ t, (d t).compact = K) (hQ : ∀ theta, (Q theta).compact = K)
  (hmem : SchwartzMembershipStatement hG a ha mu d C.presentation hindex Q K hK hK hPK rho)
  (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
    (rationalXi hK hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)
  (hcompact : IsSourceCompactAt i K.toSubgroup)
  (hhaar : ∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu (K := K) p)
  (hn : DensityNonnegative hG a ha mu C.presentation Q)
  (hdense : DensityPositiveDense hG a ha mu C.presentation Q)
  (h : SynthesisInverseStatement hG a ha mu d hindex C Q hK hPK rho)

include hcompact hhaar hn hdense h in
/-- The target at the displayed inputs, as the product identity. -/
theorem fourier_synthesis (psi : Invariant) :
    Fourier (kappa psi) = rationalSemistandardThetaInvariantInclusion C psi :=
  (synthesisInverse_iff_product hG a ha mu d hindex C Q hK hPK rho).mp h hi hfin hnu hspecial hd hQ
    hmem hsw hdelta hT hcompact hhaar hn hdense psi

include hcompact hhaar hn hdense h in
/-- The identity holds at every full index, in particular off the support of
`ψ`, where the Fourier component of `κ(ψ)` vanishes. -/
theorem fourier_synthesis_eq_zero (psi : Invariant) (t : Theta) (ht : psi.val.val t = 0) :
    Fourier (kappa psi) t = 0 :=
  (congrFun (fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem
    hsw hdelta hT hcompact hhaar hn hdense h psi) t).trans ht

include hcompact hhaar hn hdense h in
/-- The Fourier family of an element of the image of `κ` is a smooth
finite-support family. -/
theorem fourier_mem_smooth_of_mem_range (f : Schwartz) (hf : f ∈ LinearMap.range kappa) :
    Fourier f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d := by
  obtain ⟨psi, rfl⟩ := hf
  rw [fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
    hdelta hT hcompact hhaar hn hdense h psi]
  exact psi.val.property

include hcompact hhaar hn hdense h in
/-- On the image of `κ`, the Fourier family has finite support. -/
theorem fourier_support_finite_of_mem_range (f : Schwartz) (hf : f ∈ LinearMap.range kappa) :
    (rationalSemistandardThetaSupport.{u, uV} a ha mu (Fourier f)).Finite :=
  ((mem_rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d _).mp
    (fourier_mem_smooth_of_mem_range hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ
      hmem hsw hdelta hT hcompact hhaar hn hdense h f hf)).2

include hcompact hhaar hn hdense h in
/-- On the image of `κ`, the Fourier family belongs to the actual invariant carrier. -/
theorem fourier_mem_invariant_of_mem_range (f : Schwartz) (hf : f ∈ LinearMap.range kappa) :
    (⟨Fourier f, fourier_mem_smooth_of_mem_range hG a ha mu d hindex C Q hK hPK rho hi hfin hnu
      hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense h f hf⟩ :
        rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) ∈ Invariant := by
  obtain ⟨psi, rfl⟩ := hf
  change IsWeylInvariant C (Fourier (kappa psi))
  rw [fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
    hdelta hT hcompact hhaar hn hdense h psi]
  exact psi.property

/-- The Fourier family restricted to the image of `κ`, as a complex-linear map
into the actual invariant carrier. Its property witnesses are derived from the
target `SynthesisInverseStatement` at the displayed inputs. -/
def fourierOnRange : LinearMap.range kappa →ₗ[ℂ] Invariant where
  toFun f := ⟨⟨Fourier f.val, fourier_mem_smooth_of_mem_range hG a ha mu d hindex C Q hK hPK rho
      hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense h f.val f.property⟩,
    fourier_mem_invariant_of_mem_range hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd
      hQ hmem hsw hdelta hT hcompact hhaar hn hdense h f.val f.property⟩
  map_add' f g := Subtype.ext (Subtype.ext (map_add (Fourier) f.val g.val))
  map_smul' c f := Subtype.ext (Subtype.ext (map_smul (Fourier) c f.val))

/-- Comparison with the product identity: the restricted inverse is the actual
Fourier family, regarded in the full dependent product. -/
theorem inclusion_fourierOnRange (f : LinearMap.range kappa) :
    rationalSemistandardThetaInvariantInclusion C
        (fourierOnRange hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw hdelta
          hT hcompact hhaar hn hdense h f) =
      Fourier f.val := rfl

/-- The restricted Fourier family is a left inverse of `κ`. -/
theorem fourierOnRange_rangeRestrict (psi : Invariant) :
    fourierOnRange hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw hdelta hT
        hcompact hhaar hn hdense h ((kappa).rangeRestrict psi) = psi :=
  Subtype.ext (Subtype.ext (fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu
    hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense h psi))

/-- `κ` composed with the restricted Fourier family is the identity of its image. -/
theorem synthesis_fourierOnRange (f : LinearMap.range kappa) :
    kappa (fourierOnRange hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
      hdelta hT hcompact hhaar hn hdense h f) = f.val := by
  obtain ⟨_, psi, rfl⟩ := f
  exact congrArg (fun x => (kappa) x) (fourierOnRange_rangeRestrict hG a ha mu d hindex C Q hK hPK
    rho hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense h psi)

include hsw hdelta hT hcompact hhaar hn hdense h in
/-- `κ` is injective. -/
theorem invariantSynthesis_injective : Function.Injective kappa := fun x y hxy =>
  rationalSemistandardThetaInvariantInclusion_injective C
    ((fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
      hdelta hT hcompact hhaar hn hdense h x).symm.trans
      ((congrArg (Fourier) hxy).trans
        (fourier_synthesis hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
          hdelta hT hcompact hhaar hn hdense h y)))

/-- `κ` is a complex-linear isomorphism onto its image, with inverse the
restricted actual Fourier family. -/
def synthesisRangeEquiv : Invariant ≃ₗ[ℂ] LinearMap.range kappa :=
  LinearEquiv.ofLinearMap (kappa).rangeRestrict
    (fourierOnRange hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw hdelta hT
      hcompact hhaar hn hdense h)
    (LinearMap.ext fun f => Subtype.ext (synthesis_fourierOnRange hG a ha mu d hindex C Q hK hPK rho
      hi hfin hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense h f))
    (LinearMap.ext fun psi => fourierOnRange_rangeRestrict hG a ha mu d hindex C Q hK hPK rho hi hfin
      hnu hspecial hd hQ hmem hsw hdelta hT hcompact hhaar hn hdense h psi)

theorem synthesisRangeEquiv_symm_apply (f : LinearMap.range kappa) :
    (synthesisRangeEquiv hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw
        hdelta hT hcompact hhaar hn hdense h).symm f =
      fourierOnRange hG a ha mu d hindex C Q hK hPK rho hi hfin hnu hspecial hd hQ hmem hsw hdelta hT
        hcompact hhaar hn hdense h f := rfl

end Consequences

end Langlands.HarishChandraSchwartz.RationalSemistandard.SynthesisInverse
