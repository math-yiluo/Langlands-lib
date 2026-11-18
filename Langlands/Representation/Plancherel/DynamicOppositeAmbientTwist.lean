import Langlands.Representation.Plancherel.UnramifiedAmbientTwist
import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.Representation.Plancherel.ContinuedIntertwiningScalarBaseChange

/-! # Ambient unramified invariance of the actual opposite scalar -/

noncomputable section

set_option maxRecDepth 2048

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe u uV uG uI

/-- A continuous unramified character kills any subgroup that is a limit
of compact subgroups, since its positive norm characters kill compact groups. -/
theorem unramifiedCharacter_isLimitOfCompactSubgroups_le_ker
    {H : Type uG} [Group H] [TopologicalSpace H]
    {I : Type uI} (ν : I → (H →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
    (eta : unramifiedCharacters ν) (U : Subgroup H)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    U ≤ eta.val.toMonoidHom.ker := by
  intro x hx
  let u : U := ⟨x, hx⟩
  obtain ⟨J, hJ, huJ⟩ := hUc {u} isCompact_singleton
  exact compactSubgroup_le_unramifiedPullback_ker ν hν U.subtype
    continuous_subtype_val eta J hJ (huJ (Set.mem_singleton u))

section TranslationScalar

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L)) (hL : IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uG} [AddCommGroup W] [Module ℂ W]
  {Ω Λ D E : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {T : Ω → V →ₗ[ℂ] W} {S : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω T) (q : RationalOperatorContinuationData Λ S)
  (tau : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
  (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω)
  (hDt : D ⊆ (unramifiedParameterTranslation _ tau) ⁻¹' Ω)
  (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ)
  (hEt : E ⊆ (unramifiedParameterTranslation _ tau) ⁻¹' Λ)
  (hT : ∀ z (hz : z ∈ D), T ⟨z, hDΩ hz⟩ = T ⟨tau * z, hDt hz⟩)
  (hS : ∀ z (hz : z ∈ E), S ⟨z, hEΛ hz⟩ = S ⟨tau * z, hEt hz⟩)

include hD hE hDt hEt hT hS

/-- Equality of the original operators at translated parameters, on separate
nonempty open sets, fixes every extracted composite fraction. -/
theorem continuedCompositeRationalScalar_fixed_of_original_translation
    (v : V) (ell : V →ₗ[ℂ] ℂ) :
    rationalUnramifiedFunctionFieldTranslation L hp hL tau
        (continuedCompositeRationalScalar L hp hL p q
          (hneD.mono hDΩ) (hneE.mono hEΛ) v ell) =
      continuedCompositeRationalScalar L hp hL p q
        (hneD.mono hDΩ) (hneE.mono hEΛ) v ell := by
  have hnT : ∀ z (hz : z ∈ D),
      (T ⟨z, hDΩ hz⟩).comp (LinearEquiv.refl ℂ V).toLinearMap =
        (LinearEquiv.refl ℂ W).toLinearMap.comp (T ⟨tau * z, hDt hz⟩) := by
    intro z hz
    simpa only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, LinearMap.id_comp]
      using hT z hz
  have hnS : ∀ z (hz : z ∈ E),
      (S ⟨z, hEΛ hz⟩).comp (LinearEquiv.refl ℂ W).toLinearMap =
        (LinearEquiv.refl ℂ V).toLinearMap.comp (S ⟨tau * z, hEt hz⟩) := by
    intro z hz
    simpa only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, LinearMap.id_comp]
      using hS z hz
  have he := continuedCompositeRationalScalar_translation_natural L hp hL p q tau p q
    (LinearEquiv.refl ℂ V) (LinearEquiv.refl ℂ W)
    hD hneD hDt hDΩ hE hneE hEt hEΛ hnT hnS v ell
  simpa only [LinearEquiv.refl_apply, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id] using he.symm

end TranslationScalar

namespace DynamicOppositeAmbientTwist

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace3
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace3
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace4
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace4
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace5
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace5
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarMeasurableSpace6
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarBorelSpace6

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)

/-- The existing ambient unramified character as a smooth character on the
canonical rational-point topology. -/
def ambientSmoothCharacter (eta : unramifiedCharacters νG) :
    SmoothCharacter ℂ (rationalPoints G) where
  toMonoidHom := eta.val.toMonoidHom
  isOpen_ker := unramifiedCharacter_isOpen_ker νG eta

/-- Restriction of an actual ambient unramified character to the represented
dynamic Levi parameter group. -/
def restrictedAmbientParameter (eta : unramifiedCharacters νG) :
    unramifiedCharacters (normCharacters χ) :=
  rationalUnramifiedCharacterRestrict (Dynamic.Affine.centralizerHom χ) eta

omit [LocallyOfFiniteType G.X.hom] in
/-- Multiplicativity in the literal parameter-chart coercions. -/
theorem parameterTransport_mul
    (z w : unramifiedCharacters (normCharacters χ)) :
    parameterTransport χ (z * w) = parameterTransport χ z * parameterTransport χ w :=
  (parameterTransport χ).map_mul z w

omit [LocallyOfFiniteType G.X.hom] in
/-- Parameter transport makes the represented restriction literal
restriction to the actual Levi subgroup. -/
theorem restrictedAmbientParameter_eval (eta : unramifiedCharacters νG) (m : levi χ) :
    (parameterTransport χ (restrictedAmbientParameter χ eta)).val m =
      eta.val (m : rationalPoints G) := by
  change eta.val
      ((parameterHomeomorph χ).symm m ≫ (Dynamic.Affine.centralizerHom χ).hom.hom) =
    eta.val (m : rationalPoints G)
  have hm := dynamicCentralizerPointHomeomorph_apply_coe F G χ
    ((parameterHomeomorph χ).symm m)
  change ((parameterHomeomorph χ) ((parameterHomeomorph χ).symm m) : rationalPoints G) =
    ((parameterHomeomorph χ).symm m ≫ (Dynamic.Affine.centralizerHom χ).hom.hom) at hm
  rw [(parameterHomeomorph χ).apply_symm_apply] at hm
  exact congrArg eta.val hm.symm

variable (hG : IsConnectedReductive G) (eta : unramifiedCharacters νG)

include hG in
/-- Every actual ambient unramified character kills the source radical. -/
theorem ambientSmoothCharacter_radical :
    radical χ ≤ (ambientSmoothCharacter eta).toMonoidHom.ker :=
  unramifiedCharacter_isLimitOfCompactSubgroups_le_ker νG
    (fun ψ => (rationalNormContinuousCharacter G ψ).continuous) eta _
    (BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG χ)

include hG in
/-- The same statement holds for the literal opposite radical. -/
theorem ambientSmoothCharacter_oppositeRadical :
    oppositeRadical χ ≤ (ambientSmoothCharacter eta).toMonoidHom.ker :=
  ambientSmoothCharacter_radical (Dynamic.inverseCocharacter χ) hG eta

variable (K : OpenSubgroup (rationalPoints G))
  (hK : IsCompact (K : Set (rationalPoints G)))

include hK in
/-- Actual ambient unramified characters are trivial on the chosen compact
subgroup; this is proved from their norm-kernel condition. -/
theorem ambientSmoothCharacter_compact :
    K.toSubgroup ≤ (ambientSmoothCharacter eta).toMonoidHom.ker := by
  intro k hk
  apply eta.property
  apply (mem_commonNormKernel νG k).mpr
  intro ψ
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact
    ((rationalNormCharacters G ψ).toMul)
    (rationalNormContinuousCharacter G ψ).continuous K.toSubgroup hK hk

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "τ" => restrictedAmbientParameter χ eta
local notation "etas" => ambientSmoothCharacter eta
local notation "τM" => parameterTransport χ τ
local notation "νM" => leviNormCharacters χ

include hG in
/-- The forward full convergence region is invariant under restriction of
every actual ambient unramified character. -/
theorem forwardFullDomainRegion_ambient_mul_iff
    (z : unramifiedCharacters (normCharacters χ)) :
    τ * z ∈ forwardFullDomainRegion χ K hK A ↔
      z ∈ forwardFullDomainRegion χ K hK A := by
  have he := domain_eq_top_ambientParameter_iff
    (decomposition χ) (radical_isClosed χ) νM etas
    (ambientSmoothCharacter_radical χ hG eta) τM
    (fun m => (restrictedAmbientParameter_eval χ eta m).symm)
    A (parameterTransport χ z) (oppositeRadical χ)
    (ambientSmoothCharacter_oppositeRadical χ hG eta) (forwardQuotientMeasure χ K hK)
  rw [← parameterTransport_mul χ τ z] at he
  exact he

include hG in
/-- The reverse full convergence region has the same ambient invariance. -/
theorem reverseFullDomainRegion_ambient_mul_iff
    (z : unramifiedCharacters (normCharacters χ)) :
    τ * z ∈ reverseFullDomainRegion χ K hK A ↔
      z ∈ reverseFullDomainRegion χ K hK A := by
  have he := domain_eq_top_ambientParameter_iff
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ) νM etas
    (ambientSmoothCharacter_oppositeRadical χ hG eta) τM
    (fun m => (restrictedAmbientParameter_eval χ eta m).symm)
    A (parameterTransport χ z) (radical χ)
    (ambientSmoothCharacter_radical χ hG eta) (reverseQuotientMeasure χ K hK)
  rw [← parameterTransport_mul χ τ z] at he
  exact he

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : ∀ g : rationalPoints G,
    ∃ p : parabolic χ, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (hOppK : ∀ g : rationalPoints G,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : rationalPoints G) * (k : rationalPoints G))

/-- Actual forward compact integrals at parameters differing by a restricted
ambient unramified character coincide, with no change in Haar scale. -/
theorem conditionalForwardCompactFamily_ambient_mul
    (z : unramifiedCharacters (normCharacters χ))
    (hz : z ∈ forwardFullDomainRegion χ K hK A)
    (hτz : τ * z ∈ forwardFullDomainRegion χ K hK A) :
    conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A ⟨τ * z, hτz⟩ =
      conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A ⟨z, hz⟩ := by
  have he := standardCompactOperator_ambientParameter
    (decomposition χ) (radical_isClosed χ) νM etas
    (ambientSmoothCharacter_radical χ hG eta) τM
    (fun m => (restrictedAmbientParameter_eval χ eta m).symm)
    A (parameterTransport χ z) (oppositeRadical χ)
    (ambientSmoothCharacter_oppositeRadical χ hG eta) (forwardQuotientMeasure χ K hK)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadicalHaar χ K hK) (forwardIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (radical_unimodular χ hG) (oppositeRadical_unimodular χ hG)
    K (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hK hPK hOppK
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (ambientSmoothCharacter_compact eta K hK) hz
    (by
      change domain _ _ _ (A.twist (parameterTransport χ (τ * z)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (parameterTransport χ (τ * z)))) _ = ⊤ at hτz
      rw [parameterTransport_mul χ τ z] at hτz
      exact hτz)
  simp only [← parameterTransport_mul χ τ z] at he
  exact he

/-- Actual reverse compact integrals have the same invariance. -/
theorem conditionalReverseCompactFamily_ambient_mul
    (z : unramifiedCharacters (normCharacters χ))
    (hz : z ∈ reverseFullDomainRegion χ K hK A)
    (hτz : τ * z ∈ reverseFullDomainRegion χ K hK A) :
    conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A ⟨τ * z, hτz⟩ =
      conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A ⟨z, hz⟩ := by
  have he := standardCompactOperator_ambientParameter
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ) νM etas
    (ambientSmoothCharacter_oppositeRadical χ hG eta) τM
    (fun m => (restrictedAmbientParameter_eval χ eta m).symm)
    A (parameterTransport χ z) (radical χ)
    (ambientSmoothCharacter_radical χ hG eta) (reverseQuotientMeasure χ K hK)
    (decomposition χ) (radical_isClosed χ)
    (radicalHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    (oppositeRadical_unimodular χ hG) (radical_unimodular χ hG)
    K (oppositeParabolic_isClosed χ) (parabolic_isClosed χ) hK hOppK hPK
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (oppositeProjection_continuous χ) (projection_continuous χ)
    (ambientSmoothCharacter_compact eta K hK) hz
    (by
      change domain _ _ _ (A.twist (parameterTransport χ (τ * z)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (parameterTransport χ (τ * z)))) _ = ⊤ at hτz
      rw [parameterTransport_mul χ τ z] at hτz
      exact hτz)
  simp only [← parameterTransport_mul χ τ z] at he
  exact he

variable
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)

include hDForward hDReverse

/-- Ambient invariance of the original actual integrals propagates to the
fraction extracted from their independent rational continuations. -/
theorem continuedCompositeRationalScalar_ambient_fixed
    (v : CompactInductionPicture (decomposition χ) K A)
    (ℓ : CompactInductionPicture (decomposition χ) K A →ₗ[ℂ] ℂ) :
    rationalUnramifiedFunctionFieldTranslation (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG) τ
        (continuedCompositeRationalScalar (parameterScheme χ)
          (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
          p q (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) v ℓ) =
      continuedCompositeRationalScalar (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        p q (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) v ℓ := by
  have hf : DForward ⊆
      (unramifiedParameterTranslation (normCharacters χ) τ) ⁻¹'
        forwardFullDomainRegion χ K hK A := by
    intro z hz
    exact (forwardFullDomainRegion_ambient_mul_iff χ hG eta K hK A z).mpr (hDForwardΩ hz)
  have hr : DReverse ⊆
      (unramifiedParameterTranslation (normCharacters χ) τ) ⁻¹'
        reverseFullDomainRegion χ K hK A := by
    intro z hz
    exact (reverseFullDomainRegion_ambient_mul_iff χ hG eta K hK A z).mpr (hDReverseΩ hz)
  apply continuedCompositeRationalScalar_fixed_of_original_translation (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    p q τ hDForward hneForward hDForwardΩ hf hDReverse hneReverse hDReverseΩ hr
  · intro z hz
    exact (conditionalForwardCompactFamily_ambient_mul
      χ hG eta K hK A hRefl hCST hPK hOppK z (hDForwardΩ hz) (hf hz)).symm
  · intro z hz
    exact (conditionalReverseCompactFamily_ambient_mul
      χ hG eta K hK A hRefl hCST hPK hOppK z (hDReverseΩ hz) (hr hz)).symm

variable
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hne : D.Nonempty)
  (hi : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

/-- The actual conditional canonical scalar is fixed by every unramified
character of the ambient rational-point group restricted to its Levi. -/
theorem conditionalCanonicalRationalScalar_ambient_fixed :
    rationalUnramifiedFunctionFieldTranslation (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG) τ
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) =
      conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi := by
  unfold conditionalCanonicalRationalScalar standardInductionCompositeCanonicalRationalScalar
  exact continuedCompositeRationalScalar_ambient_fixed
    χ hG eta K hK A hRefl hCST hPK hOppK p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ _ _

end DynamicOppositeAmbientTwist

end Langlands.Plancherel
