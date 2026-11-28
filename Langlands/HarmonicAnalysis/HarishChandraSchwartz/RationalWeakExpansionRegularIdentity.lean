import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionIdentityDensity
import Langlands.Representation.Aubert.General.NormalizerRegularity

/-! # The weighted identity at the regular points of the unitary orbit

`WeightedWeakExpansionDenseIdentityStatement` (module `RationalWeakExpansionIdentityDensity`)
asks for the weighted V.1.1 identity
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')` on some dense set of
points `ω` of the unitary orbit `O` of `π`. Waldspurger states Proposition V.1.1 at the
`G`-regular points of `O`. This module takes for the dense set the points `ω = π ⊗ χ` with `χ`
a unitary unramified character of `M_I(F)` for which `π ⊗ χ` is regular for the literal
normalizer of `M_I(F)` in `G(F)` (`IsNormalizerRegular`), and separates two statements:

* `RegularUnitaryTwistDenseStatement`: for a nonzero smooth representation `σ` of `M_I(F)` with
  a central character, the unitary unramified characters `χ` with `σ ⊗ χ` regular form a dense
  subset of the unitary unramified characters;
* `WeightedWeakExpansionRegularIdentityStatement`: under the premises of the identity statement,
  the weighted identity holds at every orbit point `π ⊗ χ` with `π ⊗ χ` regular;
* `weightedWeakExpansionDenseIdentity_of_regular` (proved): the two statements give
  `WeightedWeakExpansionDenseIdentityStatement`.

This file proves neither of the two statements. -/

noncomputable section

set_option maxRecDepth 8000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.WeakExpansion

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

section RegularTwists

variable (i ν) (I : Finset (SimpleRoot i ν))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

/-- **The regular unitary twists** of a smooth representation `σ` of `M_I(F)`: the unitary
unramified characters `χ` of `M_I(F)` (for the rational norm characters `leviRationalNormCharacters`)
such that `σ ⊗ χ` is regular for the literal normalizer of `M_I(F)` in `G(F)`
(`IsNormalizerRegular`: no normalizer element outside `M_I(F)` fixes the isomorphism class of
`σ ⊗ χ`). This is the derived form of Waldspurger's `G`-regularity used in the Library
(`RegularSquareIntegrableJacquetMultiplicityStatement`, `UnitaryRegularParabolicIrreducibilityStatement`). -/
def regularUnitaryTwists (σ : SmoothRep.{0, u, uV} ℂ 𝐌) : Set (unitaryUnramifiedCharacters νM) :=
  {χ | IsNormalizerRegular (σ.twist χ.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker νM ⟨χ.val, χ.property.1⟩))}

/-- **Density of the regular unitary twists.** For `G` connected reductive, `i` a maximal split
torus and `ν` generic, every nonzero smooth representation `σ` of `M_I(F)` with a central
character has a dense set of regular unitary twists (`regularUnitaryTwists`) in the group of
unitary unramified characters of `M_I(F)`. -/
def RegularUnitaryTwistDenseStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
    ∀ (σ : SmoothRep.{0, u, uV} ℂ 𝐌) [Nontrivial σ] (c : Subgroup.center 𝐌 →* ℂˣ),
      σ.HasCentralCharacter c → Dense (regularUnitaryTwists i ν I σ)

end RegularTwists

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
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsSplitComponent sc)

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
local notation "orbitMap" => discreteSeriesOrbitMap CM hCM mu νM
  (discreteSeriesClass CM hCM mu π hsq)
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

set_option maxHeartbeats 3000000 in
/-- **The pointwise weighted identity at the regular points of the orbit** (Waldspurger V.1.1,
stated at the `G`-regular points, in the weighted form of printed p.304). Under exactly the data
and premises of `WeightedWeakExpansionDenseIdentityStatement` (`π` square integrable, `I'`
proper, `K` the special maximal compact subgroup, normalizer lifts in `K`, the common source
normalization): for every section `q`, all rational extensions `E_s` of `c̃_{P'|P}(s, ·)`, all
lower sections `Ψ_s` with `IsWeightedCSection (E s) q (Ψ s)`, every `m' ∈ M'(F)` and every
unitary unramified character `χ` of `M_I(F)` in `regularUnitaryTwists` (`π ⊗ χ` regular for the
literal normalizer of `M_I(F)` in `G(F)`), the identity
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')` holds at the orbit
point `ω = π ⊗ χ` (`discreteSeriesOrbitMap`). -/
def WeightedWeakExpansionRegularIdentityStatement : Prop :=
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
    ∀ m : RationalPoint F 𝐋.X,
    ∀ χ ∈ regularUnitaryTwists i ν I π.obj,
      orbitMap χ ∈ {ω : Oπ |
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
              (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq ω) m}

omit [BorelSpace (𝐌 ⧸ CM)] in
/-- The orbit map `χ ↦ π ⊗ χ` sends a dense set of unitary unramified characters to a dense set
of orbit points: it is continuous and surjective. -/
theorem dense_orbitMap_image {X : Set (unitaryUnramifiedCharacters νM)} (hX : Dense X) :
    Dense ((orbitMap) '' X) :=
  (isOpenQuotientMap_discreteSeriesOrbitMap CM hCM mu νM
      (discreteSeriesClass CM hCM mu π hsq)).surjective.denseRange.dense_image
    (continuous_discreteSeriesOrbitMap CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)) hX

set_option maxHeartbeats 3000000 in
/-- **The identity on a dense set of orbit points.** The density of the regular unitary twists
and the identity at the regular orbit points give `WeightedWeakExpansionDenseIdentityStatement`:
the square integrability of `π` supplies a central character, irreducibility makes `π` nonzero,
and the orbit map carries the dense set of regular unitary twists onto a dense set of orbit
points, on which the identity holds. -/
theorem weightedWeakExpansionDenseIdentity_of_regular
    (hdense : RegularUnitaryTwistDenseStatement.{u, uV} (G := G) i ν I)
    (hreg : WeightedWeakExpansionRegularIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π
      mu hsq hRefl hCST PG hA R PM) :
    WeightedWeakExpansionDenseIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π
      mu hsq hRefl hCST PG hA R PM := by
  intro hprop hspec hlift hN q E Ψ hsec m
  have : Nontrivial π.obj := by
    have := (Representation.irreducible_iff_isSimpleModule_asModule
      π.obj.representation).mp π.property.1
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ 𝐌) π.obj.representation.asModule
  obtain ⟨c, -⟩ := hsq.2
  have hD : Dense (regularUnitaryTwists i ν I π.obj) :=
    hdense hG hi hν π.obj c.character c.acts
  refine (dense_orbitMap_image I sc hs π mu hsq hD).mono ?_
  rintro _ ⟨χ, hχ, rfl⟩
  -- The two sets were elaborated in different modules; they differ only in the auxiliary proof
  -- constants that Lean generates, so reducible transparency suffices.
  have h := hreg hprop hspec hlift hN q E Ψ hsec m χ hχ
  with_reducible exact h

end Langlands.HarishChandraSchwartz.WeakExpansion
