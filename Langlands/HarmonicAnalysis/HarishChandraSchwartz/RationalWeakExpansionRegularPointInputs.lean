import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionRegularIdentity

/-! # The weighted identity at a regular orbit point from four inputs

`WeightedWeakExpansionRegularIdentityStatement` (module `RationalWeakExpansionRegularIdentity`)
asserts the weighted identity
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')` at the orbit points
`ω = π ⊗ χ` with `π ⊗ χ` regular. This module separates it into the unweighted Proposition V.1.1
of Waldspurger at such a point and three auxiliary facts.

Definitions:
* `lowerCompactCFamily`: the c-family `cCompactFamily` with the compact subgroup of a lower density
  package on `M'`;
* `CExtensionAt`: a rational extension of `c_{P'|P}(s, ·)` regular at one unitary character `χ`,
  and its value `CExtensionAt.value` at `χ` (independent of the extension, `value_eq`);
* `compactCoefficient`, `lowerCompactCoefficient`: the coefficient maps `E^G_P` and
  `E^{M'}_{M'∩s·P}` read on the fixed compact pictures at a unitary character.

Statements (not proved here):
* `UnweightedRegularPointIdentityStatement`: Proposition V.1.1 at a regular orbit point, on the
  compact pictures, with the values of the extensions `CExtensionAt`;
* `CExtensionAtRegularStatement`: such extensions exist at every regular unitary character;
* `WeightedCValueRelationStatement`: `µ^{M'}(sω) c̃_{P'|P}(s, ω) = µ^G(ω) c_{P'|P}(s, ω)` for the
  values of the two kinds of extensions;
* `LowerCoefficientCompactPictureStatement`: the lower orbit coefficient of a lower section at
  `sω` is `lowerCompactCoefficient` of its compact picture.

`weightedWeakExpansionRegularIdentity_of_inputs` (proved): the four statements give
`WeightedWeakExpansionRegularIdentityStatement`. -/

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

section Extension

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

set_option maxHeartbeats 1600000 in
/-- **The c-family on the fixed compact pictures, with the lower compact subgroup of a lower
density package**: `cCompactFamily` for `π` with `K' = lowerK PM`. -/
def lowerCompactCFamily (z : cDomain hG hi hν I I' hζ hζ' n hn K hK π.obj) :
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj →ₗ[ℂ]
      ProductInducedCompactPicture (decomposition χs) (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
        (SmoothRep.pullback (eₛ).symm π.obj) :=
  cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK
    (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM)
    (lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM) π.obj z

set_option maxHeartbeats 1600000 in
/-- **A rational extension of `c_{P'|P}(s, ·)` regular at one unitary character** (Waldspurger
V.1, printed p.289: the operator `c_{P'|P}(s, ω)` is rational in `ω` and regular at the
`G`-regular points of `O`, by IV.2.2). The interior of the joint convergence domain `cDomain` is
nonempty; a global polynomial numerator `N` and a regular denominator `d` satisfy
`N(w) = d(w) c(s, π ⊗ w)` on the compact pictures at every `w` of that interior; and `d` does not
vanish at the given unitary character `z`. -/
structure CExtensionAt (z : unitaryUnramifiedCharacters νM) where
  /-- The interior of the convergence domain of the c-family is nonempty. -/
  interior_nonempty : (interior (cDomain hG hi hν I I' hζ hζ' n hn K hK π.obj)).Nonempty
  /-- The regular denominator. -/
  denominator : unramifiedRegularFunctions νM
  /-- The global polynomial numerator. -/
  numerator : unramifiedCharacters νM →
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj →ₗ[ℂ]
      ProductInducedCompactPicture (decomposition χs) (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
        (SmoothRep.pullback (eₛ).symm π.obj)
  polynomial : UnramifiedOperatorFamily.IsPolynomialOperatorOn Set.univ (fun χ => numerator χ.val)
  /-- The numerator clears the denominator of `c` on the interior of its domain. -/
  clears : ∀ w (hw : w ∈ interior (cDomain hG hi hν I I' hζ hζ' n hn K hK π.obj)),
    numerator w = denominator.val w •
      lowerCompactCFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PM
        ⟨w, interior_subset hw⟩
  /-- Regularity at the given unitary character. -/
  regular : denominator.val ⟨z.val, z.property.1⟩ ≠ 0

namespace CExtensionAt

variable {hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PM}

/-- The value `c(s, π ⊗ z) = d(z)⁻¹ N(z)` of the extension at its unitary character `z`, on the
compact pictures. -/
def value {z : unitaryUnramifiedCharacters νM}
    (C : CExtensionAt hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PM z) :=
  (C.denominator.val ⟨z.val, z.property.1⟩)⁻¹ • C.numerator ⟨z.val, z.property.1⟩

set_option maxHeartbeats 1600000 in
/-- **The value does not depend on the extension.** -/
theorem value_eq {z : unitaryUnramifiedCharacters νM}
    (C C' : CExtensionAt hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PM z) :
    C.value = C'.value :=
  leviRationalContinuation_value_eq I (lowerAmbient_isConnectedReductive hG hi hν I)
    C.interior_nonempty
    (fun w => lowerCompactCFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PM w)
    C.denominator C'.denominator C.numerator C'.numerator C.polynomial C'.polynomial
    C.clears C'.clears _ C.regular C'.regular

end CExtensionAt

set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'

set_option maxHeartbeats 1600000 in
/-- **The coefficient of a compact picture on `G`**: for a unitary character `z` of `M_I(F)` and
`φ` in the fixed compact picture `I^{K×K}_{K∩P×K∩P}(E ⊗ Ě)` of `π`, the coefficient
`E^G_P Φ = rationalInducedCoefficientMap` of the element `Φ ∈ L(π ⊗ z, P)` whose compact
picture is `φ` (the inverse of the published `productInducedCompactEquiv` at `z`). -/
def compactCoefficient (z : unitaryUnramifiedCharacters νM) :
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj →ₗ[ℂ]
      LocallyConstant (rationalPoints G) ℂ :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  rationalInducedCoefficientMap hG hi hν I hK hPK
      (π.obj.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM ⟨z.val, z.property.1⟩))
      ((SmoothRep.isAdmissible_twist_iff _ _ π.obj).mpr π.property.2) ∘ₗ
    (productInducedCompactEquiv νM
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
      (continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _)
      (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
      (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
      ⟨z.val, z.property.1⟩ π.obj).symm.toLinearEquiv.toLinearMap

attribute [local instance] DynamicInducedOrbit.dynamicInducedOrbitMeasurableSpace
  DynamicInducedOrbit.dynamicInducedOrbitBorelSpace
  DynamicInducedOrbit.dynamicInducedOrbitParabolicLocallyCompact

set_option maxHeartbeats 1600000 in
/-- **The coefficient of a lower compact picture on `M'`**: for a unitary character `z` of
`M_I(F)` and `ψ` in the fixed lower compact picture of `sπ` (compact subgroup `lowerK PM`), the
coefficient `E^{M'}_{M'∩s·P} Ψ` of the element `Ψ ∈ L^{M'}(s(π ⊗ z), M' ∩ s·P)` whose compact
picture is `ψ`, at the conjugate character `sz = lowerUnramifiedCharacterConjugation z`. -/
def lowerCompactCoefficient (z : unitaryUnramifiedCharacters νM) :
    ProductInducedCompactPicture (decomposition χs) (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
        (SmoothRep.pullback (eₛ).symm π.obj) →ₗ[ℂ]
      LocallyConstant (RationalPoint F 𝐋.X) ℂ :=
  CompactInduction.coefficientMap (G := RationalPoint F 𝐋.X) (decomposition χs)
      (radical_isClosed χs)
      ((SmoothRep.pullback (eₛ).symm π.obj).twist
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
          ⟨z.val, z.property.1⟩).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χs)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn ⟨z.val, z.property.1⟩)))
      (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
      (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM)
      (DynamicOppositeCanonicalScalar.parabolic_isClosed χs)
      (DynamicOppositeCanonicalScalar.projection_continuous χs)
      (fun g => by
        obtain ⟨p, k, hg⟩ := lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM g
        exact ⟨p, p.property, k, k.property, hg⟩)
      (fun g => RationalPointFamily.rationalReductiveUnimodularity F 𝐋 hM' standardCocharacter g)
      (DynamicInducedOrbit.parabolic_modularCharacter_eq hM' χs)
      ((SmoothRep.isAdmissible_twist_iff _ _ _).mpr
        ((lowerRepresentation hG hi hν I I' hζ n hn π).property.2)) ∘ₗ
    (productInducedCompactEquiv (leviNormCharacters χs) (decomposition χs)
      (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
      (DynamicOppositeCanonicalScalar.parabolic_isClosed χs)
      (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM)
      (DynamicInducedOrbit.leviNormCharacters_continuous χs)
      (DynamicOppositeCanonicalScalar.projection_continuous χs) (radical_isClosed χs)
      (lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM)
      (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn ⟨z.val, z.property.1⟩)
      (SmoothRep.pullback (eₛ).symm π.obj)).symm.toLinearEquiv.toLinearMap

end Extension

section Statements

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

set_option linter.overlappingInstances false in
omit [BorelSpace (𝐌 ⧸ CM)] in
set_option maxHeartbeats 3000000 in
/-- **Proposition V.1.1 at a regular orbit point, unweighted, on the compact pictures**
(Waldspurger, printed p.289). Under the premises of the weighted identity statements (`I'`
proper, `K` the special maximal compact subgroup, normalizer lifts in `K`, the common source
normalization): for every unitary unramified `χ` with `π ⊗ χ` regular, all extensions `C_s` of
`c_{P'|P}(s, ·)` regular at `χ`, every section `q` and every `m' ∈ M'(F)`, the weak constant term
`(f_ω)^w_{P'}(m')` at `ω = π ⊗ χ` is `Σ_s (E^{M'}_{M'∩s·P} c_{P'|P}(s, ω) q_ω)(m')`, where
`c_{P'|P}(s, ω) = (C s).value` acts on the compact picture of `q` at `χ` and `E^{M'}` is
`lowerCompactCoefficient`. The quotient `M(F)/C_M` carries its Borel structure (explicit
`BorelSpace` binder), so `hsq` is square integrability for a Haar measure on the topological
split-center quotient, as in Waldspurger III.1. -/
def UnweightedRegularPointIdentityStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  letI : Fintype (WeylIndex i ν (rootSet i ν I) (rootSet i ν I')) :=
    @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  LiftsInCompact I I' (K := K) R →
  SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM →
  ∀ χ ∈ regularUnitaryTwists i ν I π.obj,
  ∀ (C : ∀ s, CExtensionAt hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π (PM s) χ)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (m : RationalPoint F 𝐋.X),
    rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA q (orbitMap χ)
        (leviRationalPointHomeomorph i ν I' m) =
      ∑ s, lowerCompactCoefficient hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s) χ
        ((C s).value (sectionCompactPicture hG hi hν I hKc hPK π q χ)) m

set_option linter.overlappingInstances false in
omit [BorelSpace (𝐌 ⧸ CM)] in
set_option maxHeartbeats 3000000 in
/-- **Regularity of the c-family at the regular points** (Waldspurger, printed p.289, from
Proposition IV.2.2(ii)). If `π` is square integrable modulo `C_M` for the Haar measure `mu` on
the quotient `M(F)/C_M` with its Borel structure (explicit `BorelSpace` binder), then for every
unitary unramified `χ` with `π ⊗ χ` regular and every Weyl index `s`, the c-family
`c_{P'|P}(s, ·)` has a rational extension regular at `χ` (`CExtensionAt`). -/
def CExtensionAtRegularStatement [BorelSpace (𝐌 ⧸ CM)] : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  ∀ χ ∈ regularUnitaryTwists i ν I π.obj, ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    Nonempty (CExtensionAt hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π (PM s) χ)

set_option maxHeartbeats 3000000 in
/-- **The weighted and the unweighted values** (Waldspurger V.2.3, printed p.294:
`c̃_{P'|P}(s, ω) = µ^G(ω) µ^{M'}(sω)⁻¹ c_{P'|P}(s, ω)` as rational functions). Under the common
source normalization, for every Weyl index `s`, every extension `E` of the weighted family
`c̃_{P'|P}(s, ·)`, every unitary unramified `χ` and every extension `C` of `c_{P'|P}(s, ·)` regular
at `χ`, `µ^{M'}(sω) · E.unitaryValue χ = µ^G(ω) · C.value` at `ω = π ⊗ χ`, with the weights of
the two density packages. -/
def WeightedCValueRelationStatement : Prop :=
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ (s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'))
    (E : WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π
      PG (PM s) (hN s))
    (χ : unitaryUnramifiedCharacters νM)
    (C : CExtensionAt hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π (PM s) χ),
    lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq hRefl hCST (PM s)
        (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq (orbitMap χ)) •
        E.unitaryValue χ =
      Wπ (orbitMap χ) • C.value

set_option maxHeartbeats 3000000 in
/-- **Lower coefficients through compact pictures.** For every Weyl index `s`, every lower
section `Ψ ∈ C^∞(sO, M' ∩ s·P)`, every unitary unramified `χ` and every `m' ∈ M'(F)`, the lower
orbit coefficient `(E^{M'}_{M'∩s·P} Ψ_{sω})(m')` at `sω` (`ω = π ⊗ χ`) is
`lowerCompactCoefficient` at `χ` of the compact picture of `Ψ` at the conjugate character
`lowerCharacterConjugation χ`. -/
def LowerCoefficientCompactPictureStatement : Prop :=
  ∀ (s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'))
    (Ψ : LowerSections hG hi hν I I' hζ π hRefl hCST R PM s)
    (χ : unitaryUnramifiedCharacters νM) (m : RationalPoint F 𝐋.X),
    DynamicInducedOrbit.inducedOrbitCoefficientMap (H := 𝐋) hM' (χ_ s)
        (lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
        (lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
        (lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π)
        (lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM)
        (lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM)
        (lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu)
        (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π
          hsq) Ψ
        (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq (orbitMap χ)) m =
      lowerCompactCoefficient hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s) χ
        (dynamicSectionCompactPicture (H := 𝐋) hM' (χ_ s)
          (lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
          (lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
          (lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π) Ψ
          (DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hM' (χ_ s)
            (lowerCharacterConjugation hG hi hν I I' hζ (nₛ s) (hnₛ s) χ))) m

set_option maxHeartbeats 3000000 in
/-- **The weighted identity at the regular points from its four inputs.** The unweighted
identity at a regular point, multiplied by `µ^G(ω)`, the value relation between the weighted and
the unweighted extensions, the defining property `IsWeightedCSection` of the lower sections and
the compact-picture form of the lower coefficients give
`WeightedWeakExpansionRegularIdentityStatement`; extensions regular at the point are supplied by
`CExtensionAtRegularStatement`. -/
theorem weightedWeakExpansionRegularIdentity_of_inputs
    (hV : UnweightedRegularPointIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM)
    (hR : CExtensionAtRegularStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST R PM)
    (hW : WeightedCValueRelationStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST
      PG R PM)
    (hL : LowerCoefficientCompactPictureStatement hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R
      PM) :
    WeightedWeakExpansionRegularIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM := by
  intro hprop hspec hlift hN q E Ψ hsec m χ hχ
  let : Fintype (WeylIndex i ν (rootSet i ν I) (rootSet i ν I')) :=
    @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
  have hC := fun s => Classical.choice (hR hsq χ hχ s)
  have h1 := hV hprop hspec hlift hN χ hχ hC q m
  have h : Wπ (orbitMap χ) * rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I'
        hA q (orbitMap χ) (leviRationalPointHomeomorph i ν I' m) =
      ∑ s, lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq hRefl hCST
          (PM s) (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq (orbitMap χ)) *
        DynamicInducedOrbit.inducedOrbitCoefficientMap (H := 𝐋) hM' (χ_ s)
          (lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
          (lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
          (lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π)
          (lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM)
          (lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM)
          (lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu)
          (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π
            hsq) (Ψ s)
          (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq (orbitMap χ)) m := by
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hL s (Ψ s) χ m, hsec s χ]
    have key := congrArg
      (fun L => lowerCompactCoefficient hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s) χ
        (L (sectionCompactPicture hG hi hν I hKc hPK π q χ)) m)
      (hW hN s (E s) χ (hC s))
    simp only [LinearMap.smul_apply, map_smul, LocallyConstant.smul_apply, smul_eq_mul] at key
    exact key.symm
  -- The goal and `h` were elaborated in different modules; they differ only in the auxiliary
  -- proof constants that Lean generates, so reducible transparency suffices.
  exact Set.mem_ofPred.mpr (by with_reducible exact h)

end Statements

end Langlands.HarishChandraSchwartz.WeakExpansion
