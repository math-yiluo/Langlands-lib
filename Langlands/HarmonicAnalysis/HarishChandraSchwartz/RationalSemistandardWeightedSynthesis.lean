import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology
import Mathlib.Algebra.BigOperators.Finprod

/-! # Actual finite-support weighted semistandard synthesis -/

noncomputable section

universe u uV uI uX

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz

namespace FiniteSupportSections

section LinearTotal

variable {I : Type uI} {V : I → Type uV} [∀ i, AddCommMonoid (V i)]
  [∀ i, Module ℂ (V i)] (W : ∀ i, Submodule ℂ (V i))
  {X : Type uX} [AddCommMonoid X] [Module ℂ X] (L : ∀ i, W i →ₗ[ℂ] X)

theorem linearSummand_support_subset (f : submodule W) :
    Function.support (fun i => L i (component W i f)) ⊆ support f.val := by
  intro i hi
  change f.val i ≠ 0
  intro hz
  have hc : component W i f = 0 := Subtype.ext hz
  exact hi (by change L i (component W i f) = 0; rw [hc, map_zero])

theorem linearSummand_finite (f : submodule W) :
    (Function.support (fun i => L i (component W i f))).Finite :=
  f.property.2.subset (linearSummand_support_subset W L f)

/-- Linear assembly is an actual finite sum, because each summand vanishes
off the input family's literal finite support. -/
def totalLinear : submodule W →ₗ[ℂ] X where
  toFun f := ∑ᶠ i, L i (component W i f)
  map_add' f g := by
    simp only [map_add]
    exact finsum_add_distrib (linearSummand_finite W L f) (linearSummand_finite W L g)
  map_smul' c f := by
    simp only [map_smul]
    exact (smul_finsum' c (linearSummand_finite W L f)).symm

/-- The total is the sum over precisely the input's finite literal support. -/
theorem totalLinear_apply (f : submodule W) :
    totalLinear W L f = ∑ i ∈ f.property.2.toFinset, L i (component W i f) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact f.property.2.mem_toFinset.mpr (linearSummand_support_subset W L f hi)

end LinearTotal

end FiniteSupportSections

namespace RationalSemistandard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p)

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

variable (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

set_option hygiene false in
local notation "chi" => CommGroupScheme.groupHom r.cocharacter ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme chi
set_option hygiene false in
local notation "nuL" => normCharacters chi
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive chi hG
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback r.literalLeviHomeomorph pi.obj

/-- The exact primitive scalar inputs of the published actual density.
No coefficient, packet, stability, Schwartz or form property is a field. -/
structure OrbitPacketData where
  reflection : RelativeRootReflectionExistenceStatement.{u}
  centralCharacters : CentralSplitTorusCharacterStatement.{u}
  compact : OpenSubgroup (rationalPoints G)
  isCompact : IsCompact (compact : Set (rationalPoints G))
  factorization : ∀ g : rationalPoints G,
    ∃ p : DynamicOppositeStandardIntertwining.parabolic chi, ∃ k : compact,
      g = (p : rationalPoints G) * (k : rationalPoints G)
  oppositeFactorization : ∀ g : rationalPoints G,
    ∃ p : oppositeParabolic chi, ∃ k : compact,
      g = (p : rationalPoints G) * (k : rationalPoints G)
  forward : ForwardContinuation chi reflection centralCharacters hG compact isCompact
    factorization oppositeFactorization Aπ
  reverse : ReverseContinuation chi reflection centralCharacters hG compact isCompact
    factorization oppositeFactorization Aπ
  forwardDomain : Set (unramifiedCharacters nuL)
  forwardOpen : IsOpen forwardDomain
  forwardNonempty : forwardDomain.Nonempty
  forwardContained : forwardDomain ⊆ forwardFullDomainRegion chi compact isCompact Aπ
  reverseDomain : Set (unramifiedCharacters nuL)
  reverseOpen : IsOpen reverseDomain
  reverseNonempty : reverseDomain.Nonempty
  reverseContained : reverseDomain ⊆ reverseFullDomainRegion chi compact isCompact Aπ
  irreducibleDomain : Set (unramifiedCharacters nuL)
  irreducibleOpen : IsOpen irreducibleDomain
  irreducibleNonempty : irreducibleDomain.Nonempty
  irreducible : ∀ z ∈ irreducibleDomain,
    (UnramifiedLeviInduction (DynamicOppositeStandardIntertwining.decomposition chi)
      (radical_isClosed chi) (leviNormCharacters chi) (parameterTransport chi z) Aπ).IsIrreducible
  inverseRegular : RationalFunctionUnitaryRegular MS hMS
    (conditionalCanonicalRationalScalar chi reflection centralCharacters hG compact isCompact
      factorization oppositeFactorization Aπ forward reverse forwardNonempty forwardContained
      reverseNonempty reverseContained irreducibleNonempty irreducible)⁻¹

namespace OrbitPacketData

variable {r pi} (s : OrbitPacketData r pi) (model : LeviModel p) (d : CompactData p)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [MeasurableSpace (levi p ⧸ model.splitCenter a)] [BorelSpace (levi p ⧸ model.splitCenter a)]
  (mu : Measure (levi p ⧸ model.splitCenter a)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup (model.splitCenter a)
    (model.splitCenter_le_center a ha) pi.obj.representation mu)

/-- This is precisely the proved actual source packet, evaluated at the stored
primitive scalar inputs; no output map is selected. -/
def packetLinear : smoothOrbitSections model d pi →ₗ[ℂ] (rationalPoints G → ℂ) :=
  SourcePacket.rawWavePacketLinear hG model r d a ha hindex mu pi hsq
    s.reflection s.centralCharacters s.compact s.isCompact s.factorization s.oppositeFactorization
    s.forward s.reverse s.forwardOpen s.forwardNonempty s.forwardContained
    s.reverseOpen s.reverseNonempty s.reverseContained s.irreducibleOpen s.irreducibleNonempty
    s.irreducible s.inverseRegular

end OrbitPacketData

namespace GlobalSynthesis

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
  [∀ t, (mu t).IsHaarMeasure]
  (d : ∀ t : SemistandardSpectralIndex i, CompactData t)
  (rs : ∀ t : SemistandardSpectralIndex i, CocharacterPresentation hG t)
  (hindex : ∀ t, (RenardCartan.splitValuationImage (a t)).FiniteIndex)
  (Q : ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs theta.1)
      (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1)
        (mu theta.1) theta.2))
  (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

/-- The actual source packet at every component of the published full family. -/
def componentPacket (theta : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d theta →ₗ[ℂ]
      (rationalPoints G → ℂ) :=
  (Q theta).packetLinear (chosenLeviModel theta.1) (d theta.1)
    (a theta.1) (ha theta.1) (hindex theta.1) (mu theta.1)
    (orbitRepresentative_isSquareIntegrable (chosenLeviModel theta.1) (a theta.1)
      (ha theta.1) (mu theta.1) theta.2)

/-- The actual unquotiented source coefficient for this literal Levi. -/
def sourceWeight (t : SemistandardSpectralIndex i) : ℝ :=
  SourceConstants.unquotientedWeight (rs t) K0 hK0

/-- The actual global raw function, summed over the input's finite literal
support, with exactly c^-2 gamma^-1 |W^M|/(|W^G| |P(M)|). -/
def weightedSynthesis :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      (rationalPoints G → ℂ) :=
  FiniteSupportSections.totalLinear
    (rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d)
    (fun theta => (sourceWeight hG rs K0 hK0 theta.1 : ℂ) •
      componentPacket hG a ha mu d rs hindex Q theta)

/-- Exact finite-support evaluation of the actual weighted source integral sum. -/
theorem weightedSynthesis_apply
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) (g : rationalPoints G) :
    weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 f g =
      ∑ theta ∈ f.property.2.toFinset,
        (sourceWeight hG rs K0 hK0 theta.1 : ℂ) *
          componentPacket hG a ha mu d rs hindex Q theta
            (rationalSemistandardThetaComponent a ha mu d theta f) g := by
  have h := congrArg (fun F : rationalPoints G → ℂ => F g)
    (FiniteSupportSections.totalLinear_apply
      (rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d)
      (fun theta => (sourceWeight hG rs K0 hK0 theta.1 : ℂ) •
        componentPacket hG a ha mu d rs hindex Q theta) f)
  simp only [Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at h
  convert h using 1 <;> rfl

/-- The finite-support sum as an equality of actual functions. -/
theorem weightedSynthesis_eq_sum
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 f =
      ∑ theta ∈ f.property.2.toFinset,
        (sourceWeight hG rs K0 hK0 theta.1 : ℂ) •
          componentPacket hG a ha mu d rs hindex Q theta
            (rationalSemistandardThetaComponent a ha mu d theta f) := by
  have h := FiniteSupportSections.totalLinear_apply
    (rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d)
    (fun theta => (sourceWeight hG rs K0 hK0 theta.1 : ℂ) •
      componentPacket hG a ha mu d rs hindex Q theta) f
  simp only [LinearMap.smul_apply] at h
  convert h using 1 <;> rfl

/-- The existing orbit-section topology on this actual semistandard component. -/
abbrev ComponentTopologicalSpace (theta : RationalSemistandardTheta.{u, uV} a ha mu) :=
  have := (isClosed_parabolic theta.1).locallyCompactSpace
  OrbitSectionSpace (chosenLeviModel theta.1).normCharacters
    (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
    (chosenLeviModel theta.1).unitaryCoordinates.toMulEquiv
    (decomposition theta.1) (isClosed_radical theta.1) (d theta.1).compact
    (isClosed_parabolic theta.1) (d theta.1).isCompact
    (chosenLeviModel theta.1).continuous_normCharacters (d theta.1).projection_continuous
    (d theta.1).factorization

/-- The existing topology changes no coefficient sections. -/
def componentToSmooth (theta : RationalSemistandardTheta.{u, uV} a ha mu) :
    ComponentTopologicalSpace a ha mu d theta →ₗ[ℂ]
      rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d theta :=
  have := (isClosed_parabolic theta.1).locallyCompactSpace
  OrbitSectionSpace.toSections (chosenLeviModel theta.1).normCharacters
    (orbitRepresentative (chosenLeviModel theta.1) (a theta.1) (ha theta.1) (mu theta.1) theta.2)
    (chosenLeviModel theta.1).unitaryCoordinates.toMulEquiv
    (decomposition theta.1) (isClosed_radical theta.1) (d theta.1).compact
    (isClosed_parabolic theta.1) (d theta.1).isCompact
    (chosenLeviModel theta.1).continuous_normCharacters (d theta.1).projection_continuous
    (d theta.1).factorization

section SchwartzTarget

variable {nu : cocharacterLattice S}
  {Kbase : OpenSubgroup (rationalPoints G)} (hKbase : IsCompact (Kbase : Set (rationalPoints G)))
  (hPKbase : IsIwasawaPair (standardParabolicPoints i nu ∅) (Kbase : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

/-- The target concludes membership of the exact raw sum. Source compact
compatibilities and the already named geometric finiteness target remain
explicit; no global closure or Schwartz-valued output is assumed. -/
def SchwartzMembershipStatement : Prop :=
  SemistandardSpectralFiberFinitenessStatement.{u} → IsMaximalSplitTorus i →
    IsGenericCocharacter i nu →
    BruhatTits.SpecialCompact.SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)) →
    (∀ t, (d t).compact = K0) → (∀ theta, (Q theta).compact = K0) →
    ∀ f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d,
      weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 f ∈
        schwartzSubmodule (rationalXi hKbase hPKbase) (rationalHeight (F := F) rho)

/-- VI.3.1 component continuity concludes a lift of each actual source
packet in the existing orbit-section and Schwartz topologies. It does not
assume a Schwartz-valued packet or any continuity conclusion. -/
def ComponentContinuityStatement : Prop :=
  IsMaximalSplitTorus i → IsGenericCocharacter i nu →
    BruhatTits.SpecialCompact.SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)) →
    (∀ t, (d t).compact = K0) → (∀ theta, (Q theta).compact = K0) →
    ∀ theta : RationalSemistandardTheta.{u, uV} a ha mu,
      ∃ synth : ComponentTopologicalSpace a ha mu d theta →L[ℂ]
          RationalSchwartzSpace hKbase hPKbase rho,
        ∀ v g, synth v g = componentPacket hG a ha mu d rs hindex Q theta
          (componentToSmooth a ha mu d theta v) g

/-- Finite algebraic assembly reduces global membership to the named
component continuity target; this implication proves no new estimate. -/
theorem schwartzMembership_of_componentContinuity
    (h : ComponentContinuityStatement hG a ha mu d rs hindex Q K0 hKbase hPKbase rho) :
    SchwartzMembershipStatement hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho := by
  intro _ hi hnu hspecial hd hQ f
  classical
  rw [weightedSynthesis_eq_sum]
  apply Submodule.sum_mem
  intro theta htheta
  apply Submodule.smul_mem
  obtain ⟨synth, hsynth⟩ := h hi hnu hspecial hd hQ theta
  let v : ComponentTopologicalSpace a ha mu d theta :=
    rationalSemistandardThetaComponent a ha mu d theta f
  have hfun : (synth v : rationalPoints G → ℂ) =
      componentPacket hG a ha mu d rs hindex Q theta
        (rationalSemistandardThetaComponent a ha mu d theta f) := by
    funext g
    exact hsynth v g
  rw [← hfun]
  exact (synth v).property

/-- Joint exact target for the actual global lift and the actual component
continuous lifts; source normalization and preceding obligations stay explicit. -/
def SchwartzSynthesisStatement : Prop :=
  SchwartzMembershipStatement hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho ∧
    ComponentContinuityStatement hG a ha mu d rs hindex Q K0 hKbase hPKbase rho

/-- The conditional lift restricts the codomain of the actual sum, using only
the preceding named membership target. -/
def schwartzSynthesis
    (h : SchwartzMembershipStatement hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
    (hnu : IsGenericCocharacter i nu)
    (hspecial : BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
      (K0 : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K0) (hQ : ∀ theta, (Q theta).compact = K0) :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      RationalSchwartzSpace hKbase hPKbase rho :=
  (weightedSynthesis hG a ha mu d rs hindex Q K0 hK0).codRestrict
    (schwartzSubmodule (rationalXi hKbase hPKbase) (rationalHeight (F := F) rho))
    (h hfin hi hnu hspecial hd hQ)

/-- The conditional lift has exactly the already constructed raw values. -/
theorem schwartzSynthesis_apply
    (h : SchwartzMembershipStatement hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho)
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u}) (hi : IsMaximalSplitTorus i)
    (hnu : IsGenericCocharacter i nu)
    (hspecial : BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
      (K0 : Subgroup (rationalPoints G)))
    (hd : ∀ t, (d t).compact = K0) (hQ : ∀ theta, (Q theta).compact = K0)
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) (g : rationalPoints G) :
    schwartzSynthesis hG a ha mu d rs hindex Q K0 hK0 hKbase hPKbase rho
        h hfin hi hnu hspecial hd hQ f g =
      weightedSynthesis hG a ha mu d rs hindex Q K0 hK0 f g := rfl

end SchwartzTarget

end GlobalSynthesis

end RationalSemistandard

end Langlands.HarishChandraSchwartz
