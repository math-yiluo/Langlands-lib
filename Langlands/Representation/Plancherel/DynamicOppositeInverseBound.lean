import Langlands.Representation.Plancherel.DynamicOppositeSquareIntegrablePositivity
import Langlands.Representation.Plancherel.ContinuedScalarNormBound

/-! # A uniform inverse-scalar bound under the exact square-integrable hypotheses -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeInverseBound

open DynamicOppositeScaledAdjunction
open Aubert.General Induction UnramifiedOperatorFamily
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
  hermitianAdjunctionPointMeasurable
  hermitianAdjunctionPointBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)

/-- A single positive bound for the inverse rational scalar at all unitary
parameters where both supplied continuations are regular. -/
def UnitaryCommonRegularInverseBounded
    (f : rationalUnramifiedFunctionField (parameterScheme χ)
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : unramifiedCharacters (normCharacters χ),
    z ∈ p.regularRegion ∩ q.regularRegion →
    z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
    RationalFunctionNormBoundedAt (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG) f⁻¹ z C

/-- Coefficient unitarity and admissibility imply a uniform bound for the
inverse actual opposite scalar on its unitary common regular locus. -/
theorem unitaryCommonRegularInverseBounded_of_admissible_unitary
    (hA : A.IsAdmissible) (b : InvariantPositiveForm A.representation)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (v : A) (hv0 : v ≠ 0) :
    UnitaryCommonRegularInverseBounded χ hRefl hCST hG K hK hPK hOppK A p q
      (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  have hdag : ∀ w ∈ DForward,
      unramifiedConjInv (normCharacters χ) w ∈ reverseFullDomainRegion χ K hK A :=
    fun w hw => DynamicOppositeConjugateDomain.mem_reverseFullDomainRegion_of_forward
      χ hRefl hCST hG K hK hPK hOppK A hA b w (hDForwardΩ hw)
  obtain ⟨e, c, hc, he⟩ :=
    exists_forwardCompactFamily_eval_one_eq χ hRefl hCST hG K hK hPK hOppK A v
  have hcv : c • v ≠ 0 := smul_ne_zero hc hv0
  have hpe (z : p.regularRegion) :
      compactPictureEvalOne (oppositeDecomposition χ) K A
        (p.continuedOperator z e) = c • v :=
    continuedOperator_map_eq_of_eqOn (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG) p hDForward hneForward hDForwardΩ
      (compactPictureEvalOne (oppositeDecomposition χ) K A) e (c • v)
      (fun w hw => he ⟨w, hDForwardΩ hw⟩) z
  have he0 : e ≠ 0 := by
    intro he0
    obtain ⟨w, hw⟩ := hneForward
    have ht := hpe ⟨w, p.subset_regularRegion (hDForwardΩ hw)⟩
    rw [he0, map_zero, map_zero] at ht
    exact hcv ht.symm
  have hse := scaledSourceSesq_self_ne_zero χ K hK A b he0
  let ℓ := (b.rightFunctional v).comp
    (compactPictureEvalOne (oppositeDecomposition χ) K A)
  have ha : c * b.inner v v ≠ 0 :=
    mul_ne_zero hc (fun h0 => hv0 (b.definite v h0))
  have hconst (z : p.regularRegion) :
      ℓ (p.continuedOperator z e) = c * b.inner v v := by
    change b.rightFunctional v
      (compactPictureEvalOne (oppositeDecomposition χ) K A
        (p.continuedOperator z e)) = _
    rw [hpe z, map_smul]
    rfl
  obtain ⟨C, hC, hbound⟩ :=
    exists_continuedCompositeRationalScalar_inv_norm_bound (parameterScheme χ)
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
      (scaledSourceSesq χ K hK A b)
      (compactPictureSesq (oppositeDecomposition χ) K hK A b)
      (compactPictureInnerCore (oppositeDecomposition χ) K hK A b)
      (fun _ _ => rfl) p q hDForward hneForward hDForwardΩ hdag
      (fun w hw φ φ' => hermitianAdjunction_scaled χ hRefl hCST hG K hK hPK hOppK A b
        ⟨w, hDForwardΩ hw⟩ (hdag w hw) φ φ')
      (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) e hse _
      (conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK A
        p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi e
        ((scaledSourceSesq χ K hK A b e e)⁻¹ •
          scaledSourceSesq χ K hK A b e)
        (inv_mul_cancel₀ hse))
      ℓ (c * b.inner v v) ha hconst
  exact ⟨C, hC, fun z hz hzu =>
    hbound z hz (unramifiedConjInv_eq_self_of_mem_unitary _ hzu)⟩

/-- The original square-integrability and irreducibility-locus premises
already give the uniform common-regular unitary inverse bound. No further
unitarity, splitting, conjugate-domain or analytic estimate is assumed. -/
theorem unitaryCommonRegularInverseBounded_of_squareIntegrable
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM) :
    UnitaryCommonRegularInverseBounded χ hRefl hCST hG K hK hPK hOppK A p q
      (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  let b := DynamicOppositeSquareIntegrableForm.squareIntegrableForm χ hG A hne hi C hC μM hsq
  have hirr := DynamicOppositeSquareIntegrableForm.irreducible_of_locus χ hG A hne hi
  let := hirr
  have hv : ∃ v : A, v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation A.representation)
    apply le_antisymm bot_le
    intro v _
    change v = 0
    exact hn v
  obtain ⟨v, hv⟩ := hv
  exact unitaryCommonRegularInverseBounded_of_admissible_unitary
    χ hRefl hCST hG K hK hPK hOppK A p q hsq.1 b hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi v hv

end Langlands.Plancherel.DynamicOppositeInverseBound
