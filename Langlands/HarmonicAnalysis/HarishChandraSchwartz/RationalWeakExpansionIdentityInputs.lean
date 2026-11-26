import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets

/-! # The pointwise weighted expansion from regularity, lower sections and the identity

`WeightedWeakExpansionStatement` (module `RationalWeakExpansionTargets`; Waldspurger V.1.1 in the
form of printed p.304) asserts three things for every section `q`: rational extensions `E_s` of
the weighted c-families regular on the unitary orbit, lower sections `Ψ_s` of
`sω ↦ c̃_{P'|P}(s, ω) q_ω`, and the pointwise identity at every orbit point and every point of
`M'(F)`. This module separates the three assertions:

* `WeightedCLowerSectionStatement`: for every extension `E` of `c̃_{P'|P}(s, ·)` and every
  section `q` there is a lower section `Ψ` with `IsWeightedCSection E q Ψ`;
* `WeightedWeakExpansionIdentityStatement`: for all extensions `E_s` and lower sections `Ψ_s`
  with `IsWeightedCSection (E s) q (Ψ s)`, the pointwise identity holds at every `ω ∈ O` and every
  `m' ∈ M'(F)`;
* `weightedWeakExpansion_of_inputs` (proved): the regularity target
  `WeightedCRegularityBorelStatement` and the two statements above give
  `WeightedWeakExpansionStatement`.

The lower-section statement has exactly the binders of `WeightedCRegularityBorelStatement`, and the
identity statement exactly those of `WeightedWeakExpansionStatement`; the module uses the local
instances of `RationalWeakExpansionTargets`, so that its terms are those of the targets. This
file proves neither of the two statements. -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] targetsAmbientAffine targetsLeviAffineHom targetsLeviAffine
  targetsLeviFiniteType

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

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐋I" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ 𝐋I) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ T.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)
set_option hygiene false in
local notation "Wπ" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  PG.K PG.hK PG.hPK PG.hOppK PG.p PG.q PG.hDForward PG.hneForward PG.hDForwardΩ PG.hDReverse
  PG.hneReverse PG.hDReverseΩ PG.hD PG.hne PG.hirr PG.hreg
set_option hygiene false in
local notation "χ_" s => lowerCocharacter i ν (rootSet i ν I') ζ (R.normalizer s)
set_option hygiene false in
local notation "nₛ" => R.normalizer
set_option hygiene false in
local notation "hnₛ" => R.levi_le

set_option linter.overlappingInstances false in
omit [BorelSpace (𝐌 ⧸ CM)] in
/-- **Lower sections of the weighted c-family** (Waldspurger, printed p.304). For `π` square
integrable modulo `C_M` on the Borel quotient `M_I(F)/C_M`, `I'` proper, `K` the special maximal
compact subgroup and the common source normalization: for every Weyl index `s`, every rational
extension `E` of `c̃_{P'|P}(s, ·)` regular on the unitary orbit and every section
`q ∈ C^∞(O, P)`, there is a lower smooth section `Ψ ∈ C^∞(sO, M' ∩ s·P)` with
`IsWeightedCSection E q Ψ`, that is, the section `sω ↦ c̃_{P'|P}(s, ω) q_ω`. -/
def WeightedCLowerSectionStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ (s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'))
    (E : WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π PG (PM s)
      (hN s))
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π),
    ∃ Ψ : LowerSections hG hi hν I I' hζ π hRefl hCST R PM s,
      IsWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π (nₛ s) (hnₛ s) hRefl hCST PG (PM s)
        (hN s) E q Ψ

set_option maxHeartbeats 3000000 in
/-- **The pointwise weighted identity for given extensions and lower sections** (Waldspurger V.1.1
in the form of printed p.304). For `π` square integrable (argument `hsq`), `I'` proper, `K` the
special maximal compact subgroup, normalizer lifts in `K` and the common source normalization:
for every section `q`, all rational extensions `E_s` of `c̃_{P'|P}(s, ·)` and all lower sections
`Ψ_s` with `IsWeightedCSection (E s) q (Ψ s)`, at **every** `ω ∈ O` and every `m' ∈ M'(F)`
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')`. -/
def WeightedWeakExpansionIdentityStatement : Prop :=
  letI : Fintype (WeylIndex i ν (rootSet i ν I) (rootSet i ν I')) :=
    @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  LiftsInCompact I I' (K := K) R →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (E : ∀ s, WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π
      PG (PM s) (hN s))
    (Ψ : ∀ s, LowerSections hG hi hν I I' hζ π hRefl hCST R PM s),
    (∀ s, IsWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π (nₛ s) (hnₛ s) hRefl hCST PG (PM s)
      (hN s) (E s) q (Ψ s)) →
    ∀ (ω : Oπ) (m : RationalPoint F 𝐋.X),
      Wπ ω * rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA q ω
          (leviRationalPointHomeomorph i ν I' m) =
        ∑ s, lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq hRefl hCST
            (PM s) (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq ω) *
          DynamicInducedOrbit.inducedOrbitCoefficientMap (H := 𝐋) hM' (χ_ s)
            (lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
            (lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
            (lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π)
            (lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM)
            (lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM)
            (lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu)
            (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π
              hsq) (Ψ s)
            (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq ω) m

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2048 in
/-- **The pointwise weighted expansion from its three inputs.** The regularity target
`WeightedCRegularityBorelStatement` supplies the extensions `E_s`,
`WeightedCLowerSectionStatement` the lower sections `Ψ_s`, and
`WeightedWeakExpansionIdentityStatement` the identity, for the same data. -/
theorem weightedWeakExpansion_of_inputs
    (hreg : WeightedCRegularityBorelStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST
      PG R PM)
    (hsec : WeightedCLowerSectionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST
      PG R PM)
    (hid : WeightedWeakExpansionIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM) :
    WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG hA
      R PM := by
  intro hprop hspec hlift hN q
  have hE := fun s => Classical.choice (hreg hsq hprop hspec hN s)
  have hΨ := fun s => hsec hsq hprop hspec hN s (hE s) q
  refine ⟨hE, fun s => (hΨ s).choose, fun s => (hΨ s).choose_spec, ?_⟩
  have h := hid hprop hspec hlift hN q hE (fun s => (hΨ s).choose) (fun s => (hΨ s).choose_spec)
  -- `h` and the goal differ only in the auxiliary proof constants elaborated in the two modules.
  with_reducible exact h

end WeakExpansion

end Langlands.HarishChandraSchwartz
