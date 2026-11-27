import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionIdentityInputs
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionContinuity

/-! # The pointwise weighted identity at every orbit point from a dense set of orbit points

`WeightedWeakExpansionIdentityStatement` (module `RationalWeakExpansionIdentityInputs`;
Waldspurger V.1.1 in the weighted form of printed p.304) asserts the identity
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')` at **every** point `ω`
of the unitary orbit `O`. Proposition V.1.1 itself is stated at the `G`-regular points only. This
module separates the passage from a dense set of orbit points to all of `O`:

* `RationalOrbitWeakTermContinuityStatement`: for every section `q ∈ C^∞(O, P)` and every
  `m' ∈ M'(F)`, the weak constant term `ω ↦ (f_ω)^w_{P'}(m')` is continuous on `O`;
* `WeightedWeakExpansionDenseIdentityStatement`: under the premises of the identity statement,
  for every `q`, all extensions `E_s` and lower sections `Ψ_s` with
  `IsWeightedCSection (E s) q (Ψ s)` and every `m'`, the identity holds on a dense set of orbit
  points;
* `weightedWeakExpansionIdentity_of_dense` (proved): the two statements give
  `WeightedWeakExpansionIdentityStatement`.

The other continuity inputs of the proof are published: the continuity of `µ^G` on `O`
(`continuous_standardLeviPlancherelWeight`), of the lower orbit maps (`continuous_lowerOrbitMap`),
of the lower weights (`DynamicInducedOrbit.continuous_orbitPlancherelWeight`) and of the lower
coefficients (`DynamicInducedOrbit.continuous_inducedOrbitCoefficientMap`). This file proves
neither of the two statements. -/

noncomputable section

set_option maxRecDepth 8000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section WeakTermContinuity

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "M₁" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "M₂" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M₁))
  (C : Subgroup M₁) [C.Normal] (hC : C ≤ Subgroup.center M₁)
  [MeasurableSpace (M₁ ⧸ C)] (mu : Measure (M₁ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "𝒪" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "weakTerm" => rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA

/-- **Continuity of the weak constant term on the unitary orbit.** On the Borel quotient
`M_I(F)/C`, for every section `Φ ∈ C^∞(O, P)` of the induced orbit family and every
`m' ∈ M'(F)`, the weak constant term `ω ↦ (f_ω)^w_{P'}(m')` of the orbit coefficients
`f_ω = E^G_P Φ_ω` (`rationalOrbitWeakConstantTerm`) is continuous on the whole unitary orbit `O`.
No basis or Cartan covering data are assumed. -/
def RationalOrbitWeakTermContinuityStatement : Prop :=
  ∀ [BorelSpace (M₁ ⧸ C)],
    ∀ (Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (m : M₂),
      Continuous (fun ω : 𝒪 => weakTerm Φ ω m)

end WeakTermContinuity

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

set_option maxHeartbeats 3000000 in
/-- **The pointwise weighted identity on a dense set of orbit points** (Waldspurger V.1.1, stated
at the `G`-regular points, in the weighted form of printed p.304). For `π` square integrable
(argument `hsq`), `I'` proper, `K` the special maximal compact subgroup, normalizer lifts in `K`
and the common source normalization: for every section `q`, all rational extensions `E_s` of
`c̃_{P'|P}(s, ·)`, all lower sections `Ψ_s` with `IsWeightedCSection (E s) q (Ψ s)` and every
`m' ∈ M'(F)`, the set of `ω ∈ O` at which
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')` holds is dense in `O`. -/
def WeightedWeakExpansionDenseIdentityStatement : Prop :=
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
      Dense {ω : Oπ |
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

set_option hygiene false in
local notation "Index" => WeylIndex i ν (rootSet i ν I) (rootSet i ν I')
set_option hygiene false in
local notation "lowerMap[" s "]" => lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
set_option hygiene false in
local notation "lowerW[" s "]" => lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s)
  CM hCM mu π hsq hRefl hCST (PM s)
set_option hygiene false in
local notation "lowerC[" s "]" => lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "lowerhC[" s "]" => lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM
set_option hygiene false in
local notation "lowerMu[" s "]" => lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu
set_option hygiene false in
local notation "lowerπ[" s "]" => lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π
set_option hygiene false in
local notation "lowerSq[" s "]" => lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ
  (nₛ s) (hnₛ s) CM hCM mu π hsq
set_option hygiene false in
local notation "lowerKc[" s "]" => lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π
  (PM s)
set_option hygiene false in
local notation "lowerK₀[" s "]" => lowerK hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "lowerPK[" s "]" => lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST
  π (PM s)
set_option hygiene false in
local notation "lowerCoefficient[" s "]" => DynamicInducedOrbit.inducedOrbitCoefficientMap
  (H := 𝐋) hM' (χ_ s) lowerKc[s] lowerPK[s] lowerπ[s] lowerC[s] lowerhC[s] lowerMu[s] lowerSq[s]
set_option hygiene false in
local notation "weakTerm" => rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA
set_option hygiene false in
local notation "lowerNormal[" s "]" => lowerCentral_normal hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "lowerMeas[" s "]" => lowerQuotientMeasurableSpace hG hi hν I I' hζ (nₛ s) (hnₛ s)
  CM
set_option hygiene false in
local notation "lowerHaar[" s "]" => lowerMeasure_isHaarMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s)
  CM mu

set_option maxHeartbeats 2200000 in
/-- The lower weight `µ^{M'}` is continuous on the lower orbit `sO`. -/
private theorem continuous_lowerWeight (s : Index) : Continuous lowerW[s] :=
  @DynamicInducedOrbit.continuous_orbitPlancherelWeight _ _ _ _ _ _ _ _ _
    (Standard.leviTorusHom i ν (rootSet i ν I'))
    (conjugatedCocharacter i ζ (nₛ s)) hRefl hCST hM' lowerπ[s]
    lowerC[s] lowerNormal[s] lowerhC[s] lowerMeas[s] lowerMu[s] lowerHaar[s]
    lowerSq[s] (PM s)

set_option maxHeartbeats 5200000 in
/-- The lower coefficient of a lower section at a fixed point of `M'(F)`, pulled back along
`ω ↦ sω`, is continuous on `O`. -/
private theorem continuous_lowerCoefficient_comp (s : Index)
    (Ψ : LowerSections hG hi hν I I' hζ π hRefl hCST R PM s) (x : RationalPoint F 𝐋.X) :
    Continuous (fun ω : Oπ => lowerCoefficient[s] Ψ (lowerMap[s] ω) x) := by
  have h : Continuous (fun ω => lowerCoefficient[s] Ψ ω x) :=
    @DynamicInducedOrbit.continuous_inducedOrbitCoefficientMap F _ _ _ _ 𝐋 _ _ hM' (χ_ s)
      lowerK₀[s] lowerKc[s] lowerPK[s] lowerπ[s] lowerC[s] lowerNormal[s] lowerhC[s]
      lowerMeas[s] lowerMu[s] lowerHaar[s] lowerSq[s] Ψ x
  exact h.comp (continuous_lowerOrbitMap hG hi hν I I' hζ sc hs π mu hsq R s)

set_option maxHeartbeats 2600000 in
/-- The right side of the identity, `ω ↦ Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')`, is
continuous on `O`. -/
private theorem continuous_lowerWeightedSum
    (Ψ : ∀ s, LowerSections hG hi hν I I' hζ π hRefl hCST R PM s) (x : RationalPoint F 𝐋.X) :
    letI : Fintype Index :=
      @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
    Continuous (fun ω : Oπ => ∑ s, lowerW[s] (lowerMap[s] ω) * lowerCoefficient[s] (Ψ s)
      (lowerMap[s] ω) x) := by
  refine continuous_finsetSum _ fun s _ => ?_
  exact ((continuous_lowerWeight hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R PM s).comp
    (continuous_lowerOrbitMap hG hi hν I I' hζ sc hs π mu hsq R s)).mul
    (continuous_lowerCoefficient_comp hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R PM s (Ψ s) x)

/-- Two continuous complex functions that agree on a dense set agree everywhere. -/
private theorem forall_eq_of_dense_setOf_eq {X : Type*} [TopologicalSpace X] {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hd : Dense {x | f x = g x}) :
    ∀ x, f x = g x :=
  fun x => congrFun (hf.ext_on hd hg fun _ h => h) x

set_option maxHeartbeats 1000000 in
/-- **The identity at every orbit point.** The weak-term continuity and the identity on a dense
set of orbit points give `WeightedWeakExpansionIdentityStatement`: both sides of the identity are
continuous on `O`, and they agree on a dense set. -/
theorem weightedWeakExpansionIdentity_of_dense
    (hcont : RationalOrbitWeakTermContinuityStatement hG hi hν I I' hKc hPK π CM hCM mu hsq hA)
    (hdense : WeightedWeakExpansionDenseIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π
      mu hsq hRefl hCST PG hA R PM) :
    WeightedWeakExpansionIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM := by
  intro hprop hspec hlift hN q E Ψ hsec ω m
  have hW : Continuous Wπ :=
    continuous_standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
      PG.K PG.hK PG.hPK PG.hOppK PG.p PG.q PG.hDForward PG.hneForward PG.hDForwardΩ PG.hDReverse
      PG.hneReverse PG.hDReverseΩ PG.hD PG.hne PG.hirr PG.hreg
  have hc := hcont q (leviRationalPointHomeomorph i ν I' m)
  have hg := continuous_lowerWeightedSum hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R PM Ψ m
  have hD := hdense hprop hspec hlift hN q E Ψ hsec m
  revert ω
  refine forall_eq_of_dense_setOf_eq ?_ ?_ ?_
  · exact hW.mul hc
  -- The right sides and the dense set were elaborated in different modules; they differ only in
  -- the auxiliary proof constants that Lean generates, so reducible transparency suffices.
  · with_reducible exact hg
  · with_reducible exact hD

end WeakExpansion

end Langlands.HarishChandraSchwartz
