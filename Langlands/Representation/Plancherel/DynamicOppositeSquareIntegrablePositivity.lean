import Langlands.Representation.Plancherel.DynamicOppositeScaledAdjunction
import Langlands.Representation.Plancherel.DynamicOppositeSquareIntegrableForm
import Langlands.Representation.Plancherel.DynamicOppositeUniformNonvanishing

/-! # Exact square-integrable hypotheses imply nonzero scalar and common-regular positivity -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicOppositeSquareIntegrablePositivity

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

/-- The positive compact source form obtained directly from the exact
square-integrability and nonempty irreducibility-locus premises. -/
def squareIntegrableSourceSesq
    {D : Set (unramifiedCharacters (normCharacters χ))} (hne : D.Nonempty)
    (hi : ∀ z ∈ D, (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM) :
    CompactInductionPicture (decomposition χ) K A →ₗ⋆[ℂ]
      CompactInductionPicture (decomposition χ) K A →ₗ[ℂ] ℂ :=
  scaledSourceSesq χ K hK A
    (DynamicOppositeSquareIntegrableForm.squareIntegrableForm χ hG A hne hi C hC μM hsq)

/-- Strict positivity at every unitary common regular point from admissible
coefficient unitarity, with neither splitting nor conjugate-domain assumptions. -/
theorem posAt_of_admissible_unitary
    (hA : A.IsAdmissible)
    (b : InvariantPositiveForm A.representation)
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
    (v : A) (hv0 : v ≠ 0)
    (z : unramifiedCharacters (normCharacters χ))
    (hz : z ∈ p.regularRegion ∩ q.regularRegion)
    (hzu : z.val ∈ unitaryUnramifiedCharacters (normCharacters χ)) :
    RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG)
      (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z :=
  have hdag : ∀ w ∈ DForward,
      unramifiedConjInv (normCharacters χ) w ∈ reverseFullDomainRegion χ K hK A :=
    fun w hw => DynamicOppositeConjugateDomain.mem_reverseFullDomainRegion_of_forward
      χ hRefl hCST hG K hK hPK hOppK A hA b w (hDForwardΩ hw)
  (exists_forwardCompactFamily_eval_one_eq χ hRefl hCST hG K hK hPK hOppK A v).elim fun e he =>
  he.elim fun c hc =>
  have hcv : c • v ≠ 0 := smul_ne_zero hc.1 hv0
  have hpe : compactPictureEvalOne (oppositeDecomposition χ) K A
      (p.continuedOperator ⟨z, hz.1⟩ e) = c • v :=
    continuedOperator_map_eq_of_eqOn (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG) p hDForward hneForward hDForwardΩ
      (compactPictureEvalOne (oppositeDecomposition χ) K A) e (c • v)
      (fun w hw => hc.2 ⟨w, hDForwardΩ hw⟩) ⟨z, hz.1⟩
  have hpz : p.continuedOperator ⟨z, hz.1⟩ e ≠ 0 := fun h0 => hcv (by rw [← hpe, h0, map_zero])
  have he0 : e ≠ 0 := fun h0 => hpz (by rw [h0, map_zero])
  have hse := scaledSourceSesq_self_ne_zero χ K hK A b he0
  continuedCompositeRationalScalar_posAt (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    (scaledSourceSesq χ K hK A b)
    (compactPictureSesq (oppositeDecomposition χ) K hK A b)
    (scaledSourceSesq_self χ K hK A b)
    (compactPictureHermitianPairing_self (oppositeDecomposition χ) K hK A b)
    (fun _ hu => compactPictureHermitianPairing_self_ne_zero (oppositeDecomposition χ) K hK A b hu)
    p q hDForward hneForward hDForwardΩ hdag
    (fun w hw φ φ' => hermitianAdjunction_scaled χ hRefl hCST hG K hK hPK hOppK A b
      ⟨w, hDForwardΩ hw⟩ (hdag w hw) φ φ')
    (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) e hse _
    (conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK A
      p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi e
      ((scaledSourceSesq χ K hK A b e e)⁻¹ •
        scaledSourceSesq χ K hK A b e)
      (inv_mul_cancel₀ hse))
    z hz (unramifiedConjInv_eq_self_of_mem_unitary _ hzu) hpz

/-- The scalar is nonzero and it and its inverse have positive real values
at unitary common regular points. -/
theorem unitaryPositive_of_admissible_unitary
    (hA : A.IsAdmissible)
    (b : InvariantPositiveForm A.representation)
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
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi ≠ 0 ∧
      ∀ z : unramifiedCharacters (normCharacters χ),
        z ∈ p.regularRegion ∩ q.regularRegion →
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z ∧
          RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z :=
  have hpos := fun z hz hzu => posAt_of_admissible_unitary χ hRefl hCST hG K hK
    hPK hOppK A p q hA b hDForward hneForward hDForwardΩ hDReverse hneReverse
    hDReverseΩ hD hne hi v hv0 z hz hzu
  ⟨(exists_unitary_mem_regularRegion_inter χ hRefl hCST hG K hK hPK hOppK A p q
      (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ)).elim
      fun z hz => (hpos z hz.1 hz.2).ne_zero,
    fun z hz hzu => ⟨hpos z hz hzu, (hpos z hz hzu).inv⟩⟩

/-- The exact square-integrability and irreducibility-locus hypotheses of
the final scalar target imply nonvanishing and common-regular positivity. -/
theorem unitaryPositive_of_squareIntegrable
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
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi ≠ 0 ∧
      ∀ z : unramifiedCharacters (normCharacters χ),
        z ∈ p.regularRegion ∩ q.regularRegion →
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z ∧
          RationalFunctionPosAt (parameterScheme χ) (parameterProjection_continuous χ)
            (parameterScheme_isConnectedReductive χ hG)
            (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
              p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z := by
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
  exact unitaryPositive_of_admissible_unitary χ hRefl hCST hG K hK hPK hOppK A p q
    hsq.1 b hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi v hv


end Langlands.Plancherel.DynamicOppositeSquareIntegrablePositivity
