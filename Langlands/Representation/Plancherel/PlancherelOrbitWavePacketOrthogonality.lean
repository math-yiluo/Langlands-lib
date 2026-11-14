import Langlands.Representation.Plancherel.PlancherelWeightPositivity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketOrthogonalityDense

/-! # The Plancherel product on `C^∞(O, P)` and detection by Plancherel wave packets

Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), §VII.2 (printed p. 319), defines a hermitian product on
`C^∞(Θ)_inv` as a sum, with positive coefficients, of the products
`∫_O µ(ω) (ψ'[O,P]_ω, ψ[O,P]_ω) dω` over the pairs `(O, P)`, where `µ` is the Plancherel density
of §V.2. Wave-packet detection of `ψ_f[O, P]` is the deduction in the proof of Corollary VII.2.3.
This module proves both statements for a single pair `(O, P)`, with Waldspurger's weight `µ`
itself. Here `P = P_I(F) = M_I(F) ⋉ U_I(F)` is an actual standard parabolic subgroup and `O` is
the orbit under `Im X(M_I)` of a square-integrable representation `π` of `M_I(F)`.

The Library's orthogonality results for an everywhere-positive weight do not apply to `µ`:
`µ` can vanish where `j_P` has a unitary pole. This module combines two inputs:

* `PlancherelWeightPositivity`: the real Plancherel weight `standardLeviPlancherelWeightReal`
  on `O` is continuous and bounded above. It is nonnegative when `j_P⁻¹` has nonnegative real
  unitary values. If moreover `j_P ≠ 0`, it is positive on a dense subset of `O`.
* `RationalInducedOrbitWavePacketOrthogonalityDense`: the weighted product and wave-packet
  detection on actual points, for a bounded continuous weight `u ≥ 0` with `{u > 0}` dense.

## Main results

* `standardLeviPlancherelOrbitProductCore`: the positive definite hermitian product
  `(s, t) ↦ ∫_O µ(ω) (s_ω, t_ω) dω` on `C^∞(O, P)`, conjugate-linear in its first argument
  (`standardLeviPlancherelOrbitProductCore_inner`).
* `rationalFourierOrbitSection_eq_zero_iff_forall_pairing_standardLeviPlancherelWavePacket_eq_zero`:
  for `f ∈ C(G)`, `ψ_f[O, P] = 0` if and only if `(f_ψ, f)_G = 0` for the wave packet
  `f_ψ(g) = ∫_O µ(ω) (E_P^G ψ_ω)(g) dω` of every `ψ ∈ C^∞(O, P)`.
* `rationalInducedFourierTransform_eq_zero_of_forall_pairing_standardLeviPlancherelWavePacket_eq_zero`:
  under the same vanishing, `f̂(A, P) = 0` at every representative `A` of the orbit.

## Hypotheses

The weight `µ` is defined through the canonical scalar `j_P` of `π ∘ e`, where
`e : Z_G(ζ ∘ i)(F) ≃ M_I(F)`. Three properties of `j_P` are hypotheses here, not proved:
`j_P ≠ 0`; `j_P⁻¹` is regular at every unitary character; and the values of `j_P⁻¹` there are
nonnegative reals (Lemma V.2.1, first item, gives `µ ≥ 0`). The compact open subgroup `K` used
to define `j_P` and the compact open subgroup `Kw` of the wave packets and of `C(G)` are
independent variables. The finite measure `ρX` on `Im X(M_I)` must charge every nonempty open
set. Normalizations such as Waldspurger's Haar measures and constants are not fixed here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

section Orthogonality

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity

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

attribute [local instance] HarishChandraSchwartz.rationalWeightsIsAffine
  HarishChandraSchwartz.rationalWeightsTopology
  HarishChandraSchwartz.rationalWeightsTopologicalGroup
  HarishChandraSchwartz.rationalWeightsT2Field
  HarishChandraSchwartz.rationalWeightsLocallyCompact
  HarishChandraSchwartz.rationalWeightsMeasurableSpace
  HarishChandraSchwartz.rationalWeightsBorelSpace
  HarishChandraSchwartz.rationalInducedSecondCountable
  HarishChandraSchwartz.rationalInducedT2
  HarishChandraSchwartz.rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance plancherelOrbitOrthogonalityLeviClosed
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance plancherelOrbitOrthogonalityLeviAffine
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance plancherelOrbitOrthogonalityLeviTopology
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom ζ ≫ i)) ψ).toMul)
set_option hygiene false in
local notation "UMI" =>
  unitaryUnramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
-- `M_I(F)` as a subtype of `G(F)`, written as in the wave-packet consumers.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}
-- The root set `J` of `I`.
set_option hygiene false in
local notation "𝐉" => RationalPointFamily.rootSet i ν I

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

-- The inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`.
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
-- The orbit `O = {π ⊗ z ; z ∈ Im X(M_I)}` of the class of `π`.
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

-- The canonical scalar `j_P` of the inducing representation `π ∘ e`.
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK Aπ
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

-- The Plancherel weight on the orbit `O`.
set_option hygiene false in
local notation "wO" => standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
  hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr

-- The real Plancherel weight on the orbit `O`.
set_option hygiene false in
local notation "uO" => standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K
  hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr

/-- If `j_P⁻¹` has a nonnegative real value at every unitary character, the real Plancherel
weight, viewed as a complex function, is the Plancherel weight. -/
theorem ofReal_comp_standardLeviPlancherelWeightReal
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    (fun x : Oπ => (uO hreg x : ℂ)) = wO hreg :=
  funext (ofReal_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
    hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
    hreg hnn)

/-- An upper bound of the real Plancherel weight on the compact orbit `O`, chosen from
`exists_standardLeviPlancherelWeightReal_le`. Only its existence matters: the product
`standardLeviPlancherelOrbitProductCore` does not depend on it. -/
def standardLeviPlancherelWeightRealBound
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) : ℝ :=
  Classical.choose (exists_standardLeviPlancherelWeightReal_le hG hi hν I hζ π C hC mu hsq hRefl
    hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD
    hne hirr hreg)

/-- `standardLeviPlancherelWeightRealBound` bounds the real Plancherel weight on `O`. -/
theorem standardLeviPlancherelWeightReal_le_bound
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (x : Oπ) :
    uO hreg x ≤ standardLeviPlancherelWeightRealBound hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
      hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
      hreg :=
  Classical.choose_spec (exists_standardLeviPlancherelWeightReal_le hG hi hν I hζ π C hC mu hsq
    hRefl hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    hD hne hirr hreg) x

variable [BorelSpace (𝐌 ⧸ C)] [mu.IsInvInvariant]
  {Kw : OpenSubgroup (rationalPoints G)} (hKw : IsCompact (Kw : Set (rationalPoints G)))
  (hPKw : HarishChandraSchwartz.IsIwasawaPair (standardParabolicPoints i ν ∅)
    (Kw : Subgroup (rationalPoints G)))
  [Finite (discreteSeriesStabilizer C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))]
  [Finite (𝐌 ⧸ (commonNormKernel (RationalPointFamily.leviRationalNormCharacters i ν I) ⊔ C))]
  (ρX : Measure UMI)

/-- **The Plancherel product on `C^∞(O, P)`** (Waldspurger, VII.2, printed p. 319, the summand
`∫_O µ(ω) (ψ'[O,P]_ω, ψ[O,P]_ω) dω` for one pair `(O, P)`): for a finite measure `ρX` on
`Im X(M_I)` charging every nonempty open set, and when `j_P ≠ 0` and `j_P⁻¹` is regular with
nonnegative real values at the unitary characters,
`(s, t) ↦ ∫_O µ(ω) (s_ω, t_ω) dω` is a positive definite hermitian product on
`C^∞(O, P) = rationalInducedSmoothOrbitSections`, conjugate-linear in its first argument. It is
`rationalUnitaryOrbitWeightedProductCore_of_dense` for the real Plancherel weight. -/
@[instance_reducible]
def standardLeviPlancherelOrbitProductCore [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    InnerProductSpace.Core ℂ
      (HarishChandraSchwartz.rationalInducedSmoothOrbitSections hG hi hν I hKw hPKw π) :=
  HarishChandraSchwartz.rationalUnitaryOrbitWeightedProductCore_of_dense hG hi hν I hKw hPKw π C
    hC mu hsq ρX (uO hreg)
    (continuous_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)
    (standardLeviPlancherelWeightReal_nonneg hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      hnn)
    (dense_standardLeviPlancherelWeightReal_pos hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      hj hnn)
    (standardLeviPlancherelWeightReal_le_bound hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)

/-- The inner product of `standardLeviPlancherelOrbitProductCore` is
`∫_O µ(ω) (s_ω, t_ω) dω`, with the Plancherel weight `µ = standardLeviPlancherelWeight`. -/
theorem standardLeviPlancherelOrbitProductCore_inner [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z))
    (s t : HarishChandraSchwartz.rationalInducedSmoothOrbitSections hG hi hν I hKw hPKw π) :
    (standardLeviPlancherelOrbitProductCore hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK
        p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hKw hPKw
        ρX hreg hj hnn).inner s t =
      ∫ ω, wO hreg ω *
        (haveI := HarishChandraSchwartz.locallyCompactSpace_standardParabolicPoints_rootSet
          hG hi hν I
        unitaryOrbitProductPairing (G := rationalPoints G)
          (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
          (HarishChandraSchwartz.isSemidirectDecomposition_standard hG hi hν
            (RationalPointFamily.rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
          (HarishChandraSchwartz.isClosed_standardParabolicPoints_rootSet hG hi hν I) Kw hKw
          (HarishChandraSchwartz.factorization_subtype
            (HarishChandraSchwartz.exists_standardParabolicPoints_rootSet_mul hG hi hν I hPKw))
          (fun g =>
            RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
          (HarishChandraSchwartz.modularCharacter_standardParabolicPoints hG hi hν I rfl
            (RationalPointFamily.rootSet_subset i ν I))
          π (HarishChandraSchwartz.compactOpenCofinal_standardLevi I hKw) C hC mu hsq
          (RationalPointFamily.leviRationalNormCharacters i ν I)
          (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
          (HarishChandraSchwartz.continuous_projection_standard hG hi hν
            (RationalPointFamily.rootSet_subset i ν I) _)
          (HarishChandraSchwartz.leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv s t ω)
        ∂discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC mu
          (discreteSeriesClass C hC mu π hsq) ρX := by
  rw [← ofReal_comp_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
    hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
    hreg hnn]
  rfl

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (Kw : Subgroup (rationalPoints G)) ≤
    HarishChandraSchwartz.rationalHeightSubgroup (F := F) ρ)
  (hM : HarishChandraSchwartz.IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν 𝐉))
    ((Kw : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν 𝐉)))
  (hTA : ∀ A : UnitaryOrbitRepresentative
      (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    HarishChandraSchwartz.IsRationalLeviTempered hKw ρ hM A.val.obj)
  {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : HarishChandraSchwartz.SquareIntegrableWeight μG (HarishChandraSchwartz.rationalXi hKw hPKw)
    (HarishChandraSchwartz.rationalHeight (F := F) ρ))
  [μG.IsInvInvariant] [SigmaFinite μG]
  (hμK : μG (Kw : Set (rationalPoints G)) = 1)
  {μL : Measure 𝐌} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv 𝐌]
  [μL.IsInvInvariant] [SFinite μL]
  (hswM : HarishChandraSchwartz.SquareIntegrableWeight μL
    (HarishChandraSchwartz.rationalLeviXi hKw hM)
    (fun m => HarishChandraSchwartz.rationalHeight (F := F) ρ m))
  (hTπ : HarishChandraSchwartz.IsRationalLeviTempered hKw ρ hM π.obj)
  {νU : Measure (standardUnipotentPoints i ν 𝐉)} [νU.IsHaarMeasure]
  [νU.IsMulRightInvariant] [SFinite νU]
  (hE : HarishChandraSchwartz.ConstantTermEstimate νU
    (HarishChandraSchwartz.standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (HarishChandraSchwartz.rationalXi hKw hPKw) (HarishChandraSchwartz.rationalHeight (F := F) ρ)
    (HarishChandraSchwartz.rationalLeviXi hKw hM)
    (fun m => HarishChandraSchwartz.rationalHeight (F := F) ρ m))
  (hPKiw : ∀ (m : standardLeviPoints i ν 𝐉) (n : standardUnipotentPoints i ν 𝐉),
    (m : rationalPoints G) * n ∈ Kw ↔ (m : rationalPoints G) ∈ Kw ∧ (n : rationalPoints G) ∈ Kw)
  (hMK : μL {m : 𝐌 | (m : rationalPoints G) ∈ Kw} = 1)
  (hUK : νU {n : standardUnipotentPoints i ν 𝐉 | (n : rationalPoints G) ∈ Kw} = 1)
  {Cn : ℝ}
  (hnσ : ∀ m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I),
    ‖HarishChandraSchwartz.rationalValuationCoordinates
      (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
      (HarishChandraSchwartz.isConnectedReductive_leviScheme_rootSet hG hi hν I)
      ((RationalPointFamily.leviRationalPointHomeomorph i ν I).symm m)‖ ≤
      Cn * (1 + HarishChandraSchwartz.rationalHeight (F := F) ρ m))
  (hint : ∀ (f : HarishChandraSchwartz.RationalSchwartzSpace hKw hPKw ρ)
    (A : UnitaryOrbitRepresentative
      (RationalPointFamily.leviRationalNormCharacters i ν I) π)
    (ψ : productInducedCoefficientObject (G := rationalPoints G)
      (HarishChandraSchwartz.isSemidirectDecomposition_standard hG hi hν
        (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A.val.obj),
    Integrable
      (fun x : rationalPoints G × Kw => conj (CompactInduction.integrand
        (HarishChandraSchwartz.isSemidirectDecomposition_standard hG hi hν
          (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν 𝐉) A.val.obj Kw x.1 ψ x.2) * f x.1)
      (μG.prod (CompactInduction.measure Kw hKw)))

include hμK hswM hTπ hE hPKiw hMK hUK hnσ hint in
/-- **Plancherel wave packets detect `ψ_f[O, P]`** (the deduction in the proof of Corollary
VII.2.3, printed p. 319, for Waldspurger's weight `µ`, with Proposition VII.1.3 from
`rationalFourierOrbitSmoothSectionLinear`): when `j_P ≠ 0` and `j_P⁻¹` is regular with
nonnegative real values at the unitary characters, for `f ∈ C(G)`, `ψ_f[O, P] = 0` if and only
if `(f_ψ, f)_G = 0` for the wave packet `f_ψ(g) = ∫_O µ(ω) (E_P^G ψ_ω)(g) dω` of every
`ψ ∈ C^∞(O, P)`. -/
theorem rationalFourierOrbitSection_eq_zero_iff_forall_pairing_standardLeviPlancherelWavePacket_eq_zero
    [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z))
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤
        c * HarishChandraSchwartz.rationalLeviXi hKw hM m)
    (f : HarishChandraSchwartz.RationalSchwartzSpace hKw hPKw ρ) :
    HarishChandraSchwartz.rationalFourierOrbitSection hG hi hν I hKw hPKw ρ hρ hKρ hM π C hC mu
        hsq hTA hsw f = 0 ↔
      ∀ s : HarishChandraSchwartz.rationalInducedSmoothOrbitSections hG hi hν I hKw hPKw π,
        HarishChandraSchwartz.pairing μG
          (HarishChandraSchwartz.rationalInducedOrbitWavePacket hG hi hν I hKw hPKw π C hC mu hsq
            ρX (wO hreg) s) f = 0 := by
  rw [← ofReal_comp_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
    hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
    hreg hnn]
  exact HarishChandraSchwartz.rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
    hG hi hν I hKw hPKw π C hC mu hsq ρX (uO hreg) ρ hρ hKρ hM hTA hsw hμK hswM hTπ hE hPKiw hMK
    hUK hnσ hint
    (continuous_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)
    (standardLeviPlancherelWeightReal_nonneg hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      hnn)
    (dense_standardLeviPlancherelWeightReal_pos hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      hj hnn)
    (standardLeviPlancherelWeightReal_le_bound hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)
    hcoeff f

include hμK hswM hTπ hE hPKiw hMK hUK hnσ hint in
/-- **The conclusion of Corollary VII.2.3 at each representative, for Waldspurger's weight
`µ`**: when `j_P ≠ 0` and `j_P⁻¹` is regular with nonnegative real values at the unitary
characters, if `(f_ψ, f)_G = 0` for the wave packet `f_ψ` of weight `µ` of every
`ψ ∈ C^∞(O, P)`, then `f̂(A, P) = 0` (`rationalInducedFourierTransform`) for every
representative `A` of the orbit. -/
theorem rationalInducedFourierTransform_eq_zero_of_forall_pairing_standardLeviPlancherelWavePacket_eq_zero
    [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z))
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤
        c * HarishChandraSchwartz.rationalLeviXi hKw hM m)
    (f : HarishChandraSchwartz.RationalSchwartzSpace hKw hPKw ρ)
    (h0 : ∀ s : HarishChandraSchwartz.rationalInducedSmoothOrbitSections hG hi hν I hKw hPKw π,
      HarishChandraSchwartz.pairing μG
        (HarishChandraSchwartz.rationalInducedOrbitWavePacket hG hi hν I hKw hPKw π C hC mu hsq
          ρX (wO hreg) s) f = 0)
    (A : UnitaryOrbitRepresentative
      (RationalPointFamily.leviRationalNormCharacters i ν I) π) :
    HarishChandraSchwartz.rationalInducedFourierTransform hG hi hν I hKw hPKw ρ hρ hKρ hM A.val.obj
      C hC mu (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC mu hsq A)
      A.val.property.1 (hTA A) hsw f = 0 :=
  HarishChandraSchwartz.rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
    hG hi hν I hKw hPKw π C hC mu hsq ρX (uO hreg) ρ hρ hKρ hM hTA hsw hμK hswM hTπ hE hPKiw hMK
    hUK hnσ hint
    (continuous_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)
    (standardLeviPlancherelWeightReal_nonneg hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      hnn)
    (dense_standardLeviPlancherelWeightReal_pos hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      hj hnn)
    (standardLeviPlancherelWeightReal_le_bound hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)
    hcoeff f
    (by
      rw [ofReal_comp_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K
        hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne
        hirr hreg hnn]
      exact h0)
    A

end Orthogonality

end Langlands.Plancherel
