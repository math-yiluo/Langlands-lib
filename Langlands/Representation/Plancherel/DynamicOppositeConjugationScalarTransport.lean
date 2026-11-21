import Langlands.Representation.Plancherel.ActualConjugateLeviTwist

/-! # Transport of the continued opposite scalar in fixed compact pictures -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal BigOperators
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicOppositeConjugationScalarTransport

open UnramifiedOperatorFamily

universe u uV uW uV' uW'

section Continuation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {L L' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine L.X.left] [IsAffine L'.X.left]

local instance sourcePointTopology : TopologicalSpace (GroupScheme.rationalPoints L) :=
  rationalPointTopology F L.X

local instance targetPointTopology : TopologicalSpace (GroupScheme.rationalPoints L') :=
  rationalPointTopology F L'.X

set_option hygiene false in
local notation "X" => unramifiedCharacters (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
set_option hygiene false in
local notation "X'" => unramifiedCharacters (fun ψ => Additive.toMul (rationalNormCharacters L' ψ))

variable (e : L ≅ L')

set_option hygiene false in
local notation "push" => rationalUnramifiedCharacterTransport e
set_option hygiene false in
local notation "pull" => rationalUnramifiedCharacterRestrict e.hom
set_option hygiene false in
local notation "reg" => rationalUnramifiedRegularFunctionsEquiv e

private theorem transport_restrict (z : X') : push (pull z) = z :=
  rationalUnramifiedCharacterRestrict_transport e.symm z

private theorem transport_open_locus (P : X → Prop) (P' : X' → Prop)
    (hP : ∀ z, P z ↔ P' (push z)) (D : Set X) (hD : IsOpen D) (hne : D.Nonempty)
    (h : ∀ z ∈ D, P z) :
    ∃ D' : Set X', IsOpen D' ∧ D'.Nonempty ∧ ∀ z ∈ D', P' z := by
  refine ⟨pull ⁻¹' D, hD.preimage (pull).continuous, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hne
    refine ⟨push z, ?_⟩
    change pull (push z) ∈ D
    rwa [rationalUnramifiedCharacterRestrict_transport]
  · intro z hz
    exact transport_restrict e z ▸ (hP (pull z)).mp (h (pull z) hz)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  (eV : V ≃ₗ[ℂ] V') (eW : W ≃ₗ[ℂ] W')
  {Ω : Set X} {Ω' : Set X'}
  {A : Ω → V →ₗ[ℂ] W} {A' : Ω' → V' →ₗ[ℂ] W'}
  (hΩ : ∀ z : X, push z ∈ Ω' ↔ z ∈ Ω)
  (hA : ∀ (z : Ω) (v : V), A' ⟨push z.val, (hΩ z.val).2 z.property⟩ (eV v) =
    eW (A z v))
  (p : RationalOperatorContinuationData Ω A)

include hΩ in
private theorem restrict_mem (z : Ω') : pull z.val ∈ Ω := by
  apply (hΩ (pull z.val)).1
  rw [transport_restrict]
  exact z.property

/-- Transport the denominator through the parameter isomorphism and the numerator through
the parameter isomorphism and the two fixed linear equivalences. -/
private def transportContinuation : RationalOperatorContinuationData Ω' A' where
  denominator := reg p.denominator
  denominator_nonzero z :=
    p.denominator_nonzero ⟨pull z.val, restrict_mem e hΩ z⟩
  numerator z := eW.toLinearMap.comp ((p.numerator (pull z)).comp eV.symm.toLinearMap)
  polynomial v := by
    obtain ⟨n, b, w, hw⟩ := p.polynomial (eV.symm v)
    refine ⟨n, fun i => reg (b i), fun i => eW (w i), fun z => ?_⟩
    change eW (p.numerator (pull z.val) (eV.symm v)) =
      ∑ i, (b i).val (pull z.val) • eW (w i)
    rw [show p.numerator (pull z.val) (eV.symm v) = _ from hw ⟨_, Set.mem_univ _⟩,
      map_sum]
    simp only [map_smul]
  clears z := by
    let w : Ω := ⟨pull z.val, restrict_mem e hΩ z⟩
    have hz : (⟨push w.val, (hΩ w.val).2 w.property⟩ : Ω') = z :=
      Subtype.ext (transport_restrict e z.val)
    apply LinearMap.ext
    intro v
    change eW (p.numerator w.val (eV.symm v)) = p.denominator.val w.val • A' z v
    rw [p.clears w, LinearMap.smul_apply, map_smul, ← hA w, hz,
      LinearEquiv.apply_symm_apply]

private theorem transportContinuation_apply
    (z : (transportContinuation e eV eW hΩ hA p).regularRegion) (v : V) :
    (transportContinuation e eV eW hΩ hA p).continuedOperator z (eV v) =
      eW (p.continuedOperator ⟨pull z.val, z.property⟩ v) := by
  change (p.denominator.val (pull z.val))⁻¹ •
      eW (p.numerator (pull z.val) (eV.symm (eV v))) =
    eW ((p.denominator.val (pull z.val))⁻¹ • p.numerator (pull z.val) v)
  rw [LinearEquiv.symm_apply_apply, map_smul]

variable (hp : Continuous (rationalValuationImageProjection L)) (hL : IsConnectedReductive L)
  (hp' : Continuous (rationalValuationImageProjection L')) (hL' : IsConnectedReductive L')
  {Λ : Set X} {Λ' : Set X'}
  {B : Λ → W →ₗ[ℂ] V} {B' : Λ' → W' →ₗ[ℂ] V'}
  (hΛ : ∀ z : X, push z ∈ Λ' ↔ z ∈ Λ)
  (hB : ∀ (z : Λ) (w : W), B' ⟨push z.val, (hΛ z.val).2 z.property⟩ (eW w) =
    eV (B z w))
  (q : RationalOperatorContinuationData Λ B)

set_option hygiene false in
local notation "pT" => transportContinuation e eV eW hΩ hA p
set_option hygiene false in
local notation "qT" => transportContinuation e eW eV hΛ hB q

private theorem transportedCoefficient_apply (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (z : ↥((pT).regularRegion ∩ (qT).regularRegion)) :
    (pT).continuedCompositeScalar qT (eV v) (ℓ.comp eV.symm.toLinearMap) z =
      p.continuedCompositeScalar q v ℓ ⟨pull z.val, z.property.1, z.property.2⟩ := by
  change ℓ (eV.symm ((qT).continuedOperator ⟨z.val, z.property.2⟩
    ((pT).continuedOperator ⟨z.val, z.property.1⟩ (eV v)))) = _
  rw [transportContinuation_apply, transportContinuation_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- Coefficient extraction commutes with transport in the actual function fields. -/
private theorem transportedCoefficient_fraction
    (hΩne : Ω.Nonempty) (hΛne : Λ.Nonempty) (hΩne' : Ω'.Nonempty) (hΛne' : Λ'.Nonempty)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    continuedCompositeRationalScalar L' hp' hL' pT qT hΩne' hΛne'
        (eV v) (ℓ.comp eV.symm.toLinearMap) =
      rationalUnramifiedFunctionFieldEquiv hp hL hp' hL' e
        (continuedCompositeRationalScalar L hp hL p q hΩne hΛne v ℓ) := by
  let s := scalarCoefficientPresentation (p.continuedComposite q)
    (p.continuedComposite_rational q) v ℓ
  let t := scalarCoefficientPresentation ((pT).continuedComposite qT)
    ((pT).continuedComposite_rational qT) (eV v) (ℓ.comp eV.symm.toLinearMap)
  let sT : ScalarPresentation _
      ((pT).continuedCompositeScalar qT (eV v) (ℓ.comp eV.symm.toLinearMap)) := {
    numerator := reg s.numerator
    denominator := reg s.denominator
    denominator_nonzero := fun z =>
      s.denominator_nonzero ⟨pull z.val, z.property.1, z.property.2⟩
    clears := fun z => by
      change s.denominator.val (pull z.val) *
          (pT).continuedCompositeScalar qT (eV v) (ℓ.comp eV.symm.toLinearMap) z =
        s.numerator.val (pull z.val)
      rw [transportedCoefficient_apply]
      exact s.clears ⟨pull z.val, z.property.1, z.property.2⟩ }
  have hR := continuedCompositeRegion_nonempty L hp hL p q hΩne hΛne
  have hR' := continuedCompositeRegion_nonempty L' hp' hL' pT qT hΩne' hΛne'
  have he := ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen L' hp' hL'
    t sT hR' hR' ((pT).regularRegion_isOpen.inter (qT).regularRegion_isOpen) hR'
    (Set.Subset.rfl) (Set.Subset.rfl) (fun _ _ => rfl)
  change t.toFunctionField L' hp' hL' hR' =
    rationalUnramifiedFunctionFieldEquiv hp hL hp' hL' e (s.toFunctionField L hp hL hR)
  rw [he, sT.toFunctionField_eq_div, s.toFunctionField_eq_div, map_div₀,
    rationalUnramifiedFunctionFieldEquiv_algebraMap,
    rationalUnramifiedFunctionFieldEquiv_algebraMap]

end Continuation

section ActualOppositeScalar

open Aubert.General Induction ActualConjugateLeviTwist
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

set_option hygiene false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "Kg" => (RationalDynamicSource.conjugateCompact g K)
set_option hygiene false in
local notation "hKg" => (RationalDynamicSource.conjugateCompact_isCompact g K hK)
set_option hygiene false in
local notation "hPKg" => (conjugate_parabolic_mul_compact χ g K hPK)
set_option hygiene false in
local notation "hOppKg" => (conjugate_oppositeParabolic_mul_compact χ g K hOppK)
set_option hygiene false in
local notation "Ag" => (conjugateRepresentation χ g A)

attribute [local irreducible] rationalUnramifiedCharacterRestrict
  parameterConjugationIso conditionalForwardCompactFamily conditionalReverseCompactFamily

set_option maxHeartbeats 240000 in
private theorem conditionalCanonicalRationalScalar_transport
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K' : OpenSubgroup (RationalPoint F G.X))
    (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
    (hPK' : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic ψ, ∃ k : K', x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK' : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic ψ, ∃ k : K',
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A' : SmoothRep.{0, u, uV} ℂ (levi ψ))
    (e : parameterScheme χ ≅ parameterScheme ψ)
    (p' : ForwardContinuation ψ hRefl hCST hG K' hK' hPK' hOppK' A')
    (q' : ReverseContinuation ψ hRefl hCST hG K' hK' hPK' hOppK' A')
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters ψ))}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion ψ K' hK' A')
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion ψ K' hK' A')
    {D' : Set (unramifiedCharacters (normCharacters ψ))}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition ψ) (radical_isClosed ψ)
        (leviNormCharacters ψ) (parameterTransport ψ z) A').IsIrreducible)
    (eP : CompactInductionPicture (decomposition χ) K A ≃ₗ[ℂ]
      CompactInductionPicture (decomposition ψ) K' A')
    (eOpp : CompactInductionPicture (oppositeDecomposition χ) K A ≃ₗ[ℂ]
      CompactInductionPicture (oppositeDecomposition ψ) K' A')
    (hForward : ∀ z, rationalUnramifiedCharacterTransport e z ∈ forwardFullDomainRegion ψ K' hK' A' ↔
      z ∈ forwardFullDomainRegion χ K hK A)
    (hReverse : ∀ z, rationalUnramifiedCharacterTransport e z ∈ reverseFullDomainRegion ψ K' hK' A' ↔
      z ∈ reverseFullDomainRegion χ K hK A)
    (hForwardApply : ∀ (z : forwardFullDomainRegion χ K hK A)
      (v : CompactInductionPicture (decomposition χ) K A),
      conditionalForwardCompactFamily ψ hRefl hCST hG K' hK' hPK' hOppK' A'
        ⟨rationalUnramifiedCharacterTransport e z.val, (hForward z.val).2 z.property⟩ (eP v) =
        eOpp (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z v))
    (hReverseApply : ∀ (z : reverseFullDomainRegion χ K hK A)
      (v : CompactInductionPicture (oppositeDecomposition χ) K A),
      conditionalReverseCompactFamily ψ hRefl hCST hG K' hK' hPK' hOppK' A'
        ⟨rationalUnramifiedCharacterTransport e z.val, (hReverse z.val).2 z.property⟩ (eOpp v) =
        eP (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z v))
    (hIrreducible : ∀ z,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible ↔
      (UnramifiedLeviInduction (decomposition ψ) (radical_isClosed ψ)
        (leviNormCharacters ψ) (parameterTransport ψ (rationalUnramifiedCharacterTransport e z)) A').IsIrreducible) :
    conditionalCanonicalRationalScalar ψ hRefl hCST hG K' hK' hPK' hOppK' A'
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous ψ) (parameterScheme_isConnectedReductive ψ hG)
        e
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  let pTransport := transportContinuation
    (L := parameterScheme χ) (L' := parameterScheme ψ) e eP eOpp
    (Ω := forwardFullDomainRegion χ K hK A)
    (Ω' := forwardFullDomainRegion ψ K' hK' A')
    (A := conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A)
    (A' := conditionalForwardCompactFamily ψ hRefl hCST hG K' hK' hPK' hOppK' A')
    hForward hForwardApply p
  let qTransport := transportContinuation
    (L := parameterScheme χ) (L' := parameterScheme ψ) e eOpp eP
    (Ω := reverseFullDomainRegion χ K hK A)
    (Ω' := reverseFullDomainRegion ψ K' hK' A')
    (A := conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A)
    (A' := conditionalReverseCompactFamily ψ hRefl hCST hG K' hK' hPK' hOppK' A')
    hReverse hReverseApply q
  obtain ⟨DTransport, hDTransport, hneDTransport, hiDTransport⟩ := transport_open_locus e
    (fun z => (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (fun z => (UnramifiedLeviInduction (decomposition ψ) (radical_isClosed ψ)
      (leviNormCharacters ψ) (parameterTransport ψ z) A').IsIrreducible)
    hIrreducible D hD hne hi
  obtain ⟨v, ℓ, hℓ⟩ := exists_normalized_compactCoefficient
    (χ := χ) (hG := hG) (K := K) (hK := hK) (hPK := hPK) (A := A) (hne := hne) (hi := hi)
  have hℓg : (ℓ.comp eP.symm.toLinearMap) (eP v) = 1 := by
    change ℓ (eP.symm (eP v)) = 1
    rw [eP.symm_apply_apply, hℓ]
  have hContinuation := conditionalCanonicalRationalScalar_continuation_independent
    ψ hRefl hCST hG K' hK' hPK' hOppK' A' p' q'
    hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hne' hi'
    pTransport qTransport
  have hLocus := conditionalCanonicalRationalScalar_irreducibility_locus_independent
    ψ hRefl hCST hG K' hK' hPK' hOppK' A' pTransport qTransport
    hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'
    hneDTransport hiDTransport
  have hTarget := conditionalCanonicalRationalScalar_eq_extraction
    ψ hRefl hCST hG K' hK' hPK' hOppK' A' pTransport qTransport
    hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hDTransport hneDTransport hiDTransport
    (eP v) (ℓ.comp eP.symm.toLinearMap) hℓg
  have hSource := conditionalCanonicalRationalScalar_eq_extraction
    χ hRefl hCST hG K hK hPK hOppK A p q
    _hDForward hneForward hDForwardΩ _hDReverse hneReverse hDReverseΩ hD hne hi v ℓ hℓ
  have hFraction := transportedCoefficient_fraction
    (L := parameterScheme χ) (L' := parameterScheme ψ) e eP eOpp
    (A := conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A)
    (A' := conditionalForwardCompactFamily ψ hRefl hCST hG K' hK' hPK' hOppK' A')
    (B := conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A)
    (B' := conditionalReverseCompactFamily ψ hRefl hCST hG K' hK' hPK' hOppK' A')
    hForward hForwardApply p
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    (parameterProjection_continuous ψ) (parameterScheme_isConnectedReductive ψ hG)
    hReverse hReverseApply q
    (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ)
    (hneForward'.mono hDForwardΩ') (hneReverse'.mono hDReverseΩ') v ℓ
  exact hContinuation.trans (hLocus.trans (hTarget.trans (hFraction.trans
    (congrArg (rationalUnramifiedFunctionFieldEquiv
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
      (parameterProjection_continuous ψ) (parameterScheme_isConnectedReductive ψ hG)
      e) hSource.symm))))

/-- Full-domain covariance in the two fixed compact pictures and transport of
irreducibility suffice to compare the independently constructed canonical scalars. -/
theorem conditionalCanonicalRationalScalar_conjugation_of_compact
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (g : RationalPoint F G.X)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (p' : ForwardContinuation χg hRefl hCST hG Kg hKg hPKg hOppKg Ag)
    (q' : ReverseContinuation χg hRefl hCST hG Kg hKg hPKg hOppKg Ag)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χg))}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χg Kg hKg Ag)
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χg Kg hKg Ag)
    {D' : Set (unramifiedCharacters (normCharacters χg))}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
        (leviNormCharacters χg) (parameterTransport χg z) Ag).IsIrreducible)
    (eP : CompactInductionPicture (decomposition χ) K A ≃ₗ[ℂ]
      CompactInductionPicture (decomposition χg) Kg Ag)
    (eOpp : CompactInductionPicture (oppositeDecomposition χ) K A ≃ₗ[ℂ]
      CompactInductionPicture (oppositeDecomposition χg) Kg Ag)
    (hForward : ∀ z, conjugateParameter χ g z ∈ forwardFullDomainRegion χg Kg hKg Ag ↔
      z ∈ forwardFullDomainRegion χ K hK A)
    (hReverse : ∀ z, conjugateParameter χ g z ∈ reverseFullDomainRegion χg Kg hKg Ag ↔
      z ∈ reverseFullDomainRegion χ K hK A)
    (hForwardApply : ∀ (z : forwardFullDomainRegion χ K hK A)
      (v : CompactInductionPicture (decomposition χ) K A),
      conditionalForwardCompactFamily χg hRefl hCST hG Kg hKg hPKg hOppKg Ag
        ⟨conjugateParameter χ g z.val, (hForward z.val).2 z.property⟩ (eP v) =
        eOpp (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z v))
    (hReverseApply : ∀ (z : reverseFullDomainRegion χ K hK A)
      (v : CompactInductionPicture (oppositeDecomposition χ) K A),
      conditionalReverseCompactFamily χg hRefl hCST hG Kg hKg hPKg hOppKg Ag
        ⟨conjugateParameter χ g z.val, (hReverse z.val).2 z.property⟩ (eOpp v) =
        eP (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z v))
    (hIrreducible : ∀ z,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible ↔
      (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
        (leviNormCharacters χg) (parameterTransport χg (conjugateParameter χ g z)) Ag).IsIrreducible) :
    conditionalCanonicalRationalScalar χg hRefl hCST hG Kg hKg hPKg hOppKg Ag
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χg) (parameterScheme_isConnectedReductive χg hG)
        (parameterConjugationIso χ g)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  exact conditionalCanonicalRationalScalar_transport
    χ hRefl hCST hG K hK hPK hOppK A p q
    _hDForward hneForward hDForwardΩ _hDReverse hneReverse hDReverseΩ hD hne hi
    χg Kg hKg hPKg hOppKg Ag (parameterConjugationIso χ g) p' q'
    hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'
    eP eOpp hForward hReverse hForwardApply hReverseApply hIrreducible

end ActualOppositeScalar

end Langlands.Plancherel.DynamicOppositeConjugationScalarTransport
