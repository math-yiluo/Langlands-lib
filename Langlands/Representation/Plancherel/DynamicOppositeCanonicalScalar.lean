import Langlands.Representation.Plancherel.DynamicOppositeStandardIntertwining
import Langlands.Representation.Plancherel.StandardInductionCanonicalScalar
import Langlands.Representation.Aubert.General.DynamicInductionNormalization
import Langlands.Representation.Aubert.General.DynamicNestedParabolicTopology

/-! # Conditional rational scalar of the actual opposite standard integrals -/

noncomputable section

set_option maxRecDepth 2048

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicOppositeCanonicalScalar

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance dynamicOppositeCanonicalScalarIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance dynamicOppositeCanonicalScalarTopologicalSpace : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance dynamicOppositeCanonicalScalarT2Space : T2Space F := BruhatTits.localField_t2Space F
local instance dynamicOppositeCanonicalScalarIsTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance dynamicOppositeCanonicalScalarT2Space2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance dynamicOppositeCanonicalScalarLocallyCompactSpace : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance dynamicOppositeCanonicalScalarNonarchimedeanGroup : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance dynamicOppositeCanonicalScalarSecondCountableTopology : SecondCountableTopology F := localField_secondCountableTopology F
local instance dynamicOppositeCanonicalScalarSecondCountableTopology2 : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance centralizerClosedImmersion :
    IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom χ
local instance centralizerAffine : IsAffine (parameterScheme χ).X.left :=
  isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom χ).hom.hom.left
local instance centralizerFiniteType : LocallyOfFiniteType (parameterScheme χ).X.hom := by
  rw [← (Dynamic.Affine.centralizerHom χ).hom.hom.w]
  infer_instance
local instance dynamicOppositeCanonicalScalarTopologicalSpace2 : TopologicalSpace (RationalPoint F (parameterScheme χ).X) :=
  rationalPointTopology F (parameterScheme χ).X
local instance dynamicOppositeCanonicalScalarNonarchimedeanGroup2 : NonarchimedeanGroup (RationalPoint F (parameterScheme χ).X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup (parameterScheme χ)

/-- Continuity of the actual centralizer's valuation-image projection is proved. -/
theorem parameterProjection_continuous :
    Continuous (rationalValuationImageProjection (parameterScheme χ)) :=
  continuous_rationalValuationImageProjection (parameterScheme χ)

omit [LocallyOfFiniteType G.X.hom] in
/-- Each actual norm character is continuous in the canonical centralizer topology. -/
theorem normCharacters_continuous (ψ : rationalCharacters (parameterScheme χ)) :
    Continuous (normCharacters χ ψ) :=
  (rationalNormContinuousCharacter (parameterScheme χ) ψ).continuous

omit [LocallyOfFiniteType G.X.hom] in
/-- Closedness of the actual dynamic parabolic, in the canonical point topology. -/
theorem parabolic_isClosed : IsClosed (parabolic χ : Set (RationalPoint F G.X)) :=
  isClosed_dynamic_parabolic F G χ

omit [LocallyOfFiniteType G.X.hom] in
/-- Closedness of the literal opposite parabolic. -/
theorem oppositeParabolic_isClosed :
    IsClosed (oppositeParabolic χ : Set (RationalPoint F G.X)) :=
  isClosed_dynamic_parabolic F G (Dynamic.inverseCocharacter χ)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The actual dynamic Levi projection is continuous. -/
theorem projection_continuous : Continuous (decomposition χ).projection :=
  continuous_dynamic_projection F G χ

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The opposite projection is continuous with values in the same literal Levi. -/
theorem oppositeProjection_continuous : Continuous (oppositeDecomposition χ).projection := by
  have hc := continuous_dynamic_projection F G (Dynamic.inverseCocharacter χ)
  have transport (M : Subgroup (RationalPoint F G.X))
      (hM : levi (Dynamic.inverseCocharacter χ) = M)
      (h : IsSemidirectDecomposition (oppositeParabolic χ) M (oppositeRadical χ)) :
      Continuous h.projection := by
    subst M
    exact hc
  exact transport _ (by simp only [levi, Dynamic.centralizer_inverseCocharacter]) _

/-- Compact containment proves unimodularity of the original dynamic radical. -/
theorem radical_unimodular (hG : IsConnectedReductive G) :
    IsUnimodularModulus (radical χ) (radical_isClosed χ) :=
  DynamicNormalization.dynamicUnipotent_isUnimodular F G hG χ (radical_isClosed χ)

/-- The same proved unimodularity applies to the opposite radical. -/
theorem oppositeRadical_unimodular (hG : IsConnectedReductive G) :
    IsUnimodularModulus (oppositeRadical χ) (oppositeRadical_isClosed χ) :=
  DynamicNormalization.dynamicUnipotent_isUnimodular F G hG
    (Dynamic.inverseCocharacter χ) (oppositeRadical_isClosed χ)

local instance dynamicOppositeCanonicalScalarMeasurableSpace : MeasurableSpace (radical χ) := borel _
local instance dynamicOppositeCanonicalScalarBorelSpace : BorelSpace (radical χ) := ⟨rfl⟩
local instance dynamicOppositeCanonicalScalarMeasurableSpace2 : MeasurableSpace (oppositeRadical χ) := borel _
local instance dynamicOppositeCanonicalScalarBorelSpace2 : BorelSpace (oppositeRadical χ) := ⟨rfl⟩
local instance dynamicOppositeCanonicalScalarMeasurableSpace3 : MeasurableSpace ((radical χ).subgroupOf (oppositeRadical χ)) := borel _
local instance dynamicOppositeCanonicalScalarBorelSpace3 : BorelSpace ((radical χ).subgroupOf (oppositeRadical χ)) := ⟨rfl⟩
local instance dynamicOppositeCanonicalScalarMeasurableSpace4 : MeasurableSpace ((oppositeRadical χ).subgroupOf (radical χ)) := borel _
local instance dynamicOppositeCanonicalScalarBorelSpace4 : BorelSpace ((oppositeRadical χ).subgroupOf (radical χ)) := ⟨rfl⟩
local instance dynamicOppositeCanonicalScalarMeasurableSpace5 : MeasurableSpace (QuotientSpace (U := radical χ) (oppositeRadical χ)) :=
  borel _
local instance dynamicOppositeCanonicalScalarBorelSpace5 : BorelSpace (QuotientSpace (U := radical χ) (oppositeRadical χ)) := ⟨rfl⟩
local instance dynamicOppositeCanonicalScalarMeasurableSpace6 : MeasurableSpace (QuotientSpace (U := oppositeRadical χ) (radical χ)) :=
  borel _
local instance dynamicOppositeCanonicalScalarBorelSpace6 : BorelSpace (QuotientSpace (U := oppositeRadical χ) (radical χ)) := ⟨rfl⟩

variable
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

/-- The actual forward integral in the fixed compact picture, on its full domain. -/
def conditionalForwardCompactFamily (z : forwardFullDomainRegion χ K hK A) :
    CompactInductionPicture (decomposition χ) K A →ₗ[ℂ]
      CompactInductionPicture (oppositeDecomposition χ) K A :=
  compactIntertwiningOperator (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK
    (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) (oppositeParabolic_isClosed χ) hOppK
    (oppositeProjection_continuous χ) (parameterTransport χ z.val) A
    (conditionalForwardFamily χ K hK hRefl hCST hG A z)

/-- The reverse integral in the same fixed compact model and source Haar scale. -/
def conditionalReverseCompactFamily (z : reverseFullDomainRegion χ K hK A) :
    CompactInductionPicture (oppositeDecomposition χ) K A →ₗ[ℂ]
      CompactInductionPicture (decomposition χ) K A :=
  compactIntertwiningOperator (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K (oppositeParabolic_isClosed χ) hK hOppK
    (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (oppositeProjection_continuous χ) (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) (parabolic_isClosed χ) hPK
    (projection_continuous χ) (parameterTransport χ z.val) A
    (conditionalReverseFamily χ K hK hRefl hCST hG A z)

/-- Whole-operator continuation data for the actual forward compact integrals.
This type does not assert existence of such a continuation. -/
abbrev ForwardContinuation :=
  RationalOperatorContinuationData (forwardFullDomainRegion χ K hK A)
    (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A)

/-- Whole-operator continuation data for the reverse integrals at the same scale. -/
abbrev ReverseContinuation :=
  RationalOperatorContinuationData (reverseFullDomainRegion χ K hK A)
    (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A)

variable
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
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

local notation "L" => parameterScheme χ
local notation "hp" => parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG

local notation "scalarConstructor" =>
  standardInductionCompositeCanonicalRationalScalar L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)

/-- The canonical rational scalar for this fixed actual opposite pair and
intrinsic source Haar normalization. Convergence, continuation and generic
irreducibility are explicit inputs, not consequences of this construction. -/
def conditionalCanonicalRationalScalar :
    rationalUnramifiedFunctionField L hp hL :=
  scalarConstructor p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

local notation "c" => conditionalCanonicalRationalScalar
  χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

include hDForward hDReverse

/-- The fraction is unchanged by replacing both whole-operator continuations,
even when the two initial convergence domains do not meet. -/
theorem conditionalCanonicalRationalScalar_continuation_independent
    (p' : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q' : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A) :
    c = conditionalCanonicalRationalScalar
      χ hRefl hCST hG K hK hPK hOppK A
      p' q' hneForward hDForwardΩ hneReverse hDReverseΩ hne hi :=
  standardInductionCompositeCanonicalRationalScalar_continuation_independent L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hne hi p' q'

include hD

/-- Changing the nonempty actual irreducibility locus preserves the fraction.
Only the first locus is required to be open. -/
theorem conditionalCanonicalRationalScalar_irreducibility_locus_independent
    {D' : Set (unramifiedCharacters (normCharacters χ))} (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible) :
    c = conditionalCanonicalRationalScalar
      χ hRefl hCST hG K hK hPK hOppK A
      p q hneForward hDForwardΩ hneReverse hDReverseΩ hne' hi' :=
  standardInductionCompositeCanonicalRationalScalar_irreducibility_locus_independent L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    hne' hi'

/-- Any normalized compact coefficient extracts the same canonical fraction. -/
theorem conditionalCanonicalRationalScalar_eq_extraction
    (v : CompactInductionPicture (decomposition χ) K A)
    (ℓ : CompactInductionPicture (decomposition χ) K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    c = continuedCompositeRationalScalar L hp hL p q
      (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) v ℓ :=
  standardInductionCompositeCanonicalRationalScalar_eq_extraction L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    v ℓ hℓ

local notation "π" => SmoothRep.pullback (parameterHomeomorph χ) A
local notation "νL" => normCharacters χ

/-- The fixed-source fraction is invariant under actual inducing self-twists. -/
theorem conditionalCanonicalRationalScalar_stabilizer_fixed :
    ∀ τ : smoothRepUnramifiedTwistStabilizer νL π,
      rationalUnramifiedFunctionFieldTranslation L hp hL τ.val c = c :=
  standardInductionCompositeCanonicalRationalScalar_stabilizer_fixed L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi

/-- A finite full stabilizer gives an invariant presentation of the fraction
on the actual twist orbit. Finiteness is a separate input. -/
def conditionalCanonicalOrbitScalarPresentation
    [Finite (smoothRepUnramifiedTwistStabilizer νL π)] :
    UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) c :=
  standardInductionCompositeCanonicalOrbitScalarPresentation L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi

/-- The continued composite is an endomorphism of the actual normalized
induction on the common regular region of the two continuations. -/
def conditionalContinuedComposite (z : ↥(p.regularRegion ∩ q.regularRegion)) :
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation.IntertwiningMap
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  continuedInductionComposite L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (conditionalForwardFamily χ K hK hRefl hCST hG A)
    (conditionalReverseFamily χ K hK hRefl hCST hG A)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z

include hne hi

/-- Every normalized compact coefficient of the actual composite has a regular
presentation that specifies the continued composite on the common regular region. -/
theorem conditionalContinuedCompositeRationalScalar_spec
    (v : CompactInductionPicture (decomposition χ) K A)
    (ℓ : CompactInductionPicture (decomposition χ) K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    ∃ a b : unramifiedRegularFunctions νL,
      b ≠ 0 ∧
      (∀ z : ↥(p.regularRegion ∩ q.regularRegion), b.val z.val ≠ 0) ∧
      continuedCompositeRationalScalar L hp hL p q
          (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) v ℓ =
        algebraMap (unramifiedRegularFunctions νL)
          (rationalUnramifiedFunctionField L hp hL) a /
        algebraMap (unramifiedRegularFunctions νL)
          (rationalUnramifiedFunctionField L hp hL) b ∧
      ∀ z : ↥(p.regularRegion ∩ q.regularRegion),
        conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A
          p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z =
          (a.val z.val / b.val z.val) • Representation.IntertwiningMap.id
            (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
              (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  continuedInductionCompositeRationalScalar_spec L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (conditionalForwardFamily χ K hK hRefl hCST hG A)
    (conditionalReverseFamily χ K hK hRefl hCST hG A)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    v ℓ hℓ

omit hDForward hDReverse hD in
include hG hK hPK in
/-- The actual compact carrier has a normalized coefficient, selected from one
irreducible induction in the displayed locus. -/
theorem exists_normalized_compactCoefficient :
    ∃ (v : CompactInductionPicture (decomposition χ) K A)
      (ℓ : CompactInductionPicture (decomposition χ) K A →ₗ[ℂ] ℂ), ℓ v = 1 :=
  let s := compactInductionScalarExtraction
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) A (parameterTransport χ (Classical.choose hne))
    (hi _ (Classical.choose_spec hne))
  ⟨s.val.1, s.val.2, s.property⟩

/-- A regular presentation of the canonical fraction specifies the actual
continued composite throughout its common regular region. This requires
neither finiteness of the self-twist stabilizer nor irreducibility at the
evaluation parameter. -/
theorem conditionalCanonicalRationalScalar_spec :
    ∃ a b : unramifiedRegularFunctions νL,
      b ≠ 0 ∧
      (∀ z : ↥(p.regularRegion ∩ q.regularRegion), b.val z.val ≠ 0) ∧
      c = algebraMap (unramifiedRegularFunctions νL)
          (rationalUnramifiedFunctionField L hp hL) a /
        algebraMap (unramifiedRegularFunctions νL)
          (rationalUnramifiedFunctionField L hp hL) b ∧
      ∀ z : ↥(p.regularRegion ∩ q.regularRegion),
        conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A
          p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z =
          (a.val z.val / b.val z.val) • Representation.IntertwiningMap.id
            (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
              (leviNormCharacters χ) (parameterTransport χ z.val) A).representation := by
  have hv := exists_normalized_compactCoefficient (χ := χ) (hG := hG)
    (K := K) (hK := hK) (hPK := hPK) (A := A) (hne := hne) (hi := hi)
  obtain ⟨v, ℓ, hℓ⟩ := hv
  have hs := conditionalContinuedCompositeRationalScalar_spec
    χ hRefl hCST hG K hK hPK hOppK A
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    v ℓ hℓ
  have hc := conditionalCanonicalRationalScalar_eq_extraction
    χ hRefl hCST hG K hK hPK hOppK A
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    v ℓ hℓ
  exact hs.elim fun a ha => ha.elim fun b h =>
    ⟨a, b, h.1, h.2.1, hc.trans h.2.2.1, h.2.2.2⟩

/-- Any invariant presentation of the fraction specifies the actual continued
composite wherever that presentation's denominator is nonzero. -/
theorem conditionalContinuedComposite_eq_canonicalOrbitScalar
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) c)
    (z : ↥(p.regularRegion ∩ q.regularRegion))
    (hz : r.denominator.val z.val ≠ 0) :
    conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A
      p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z =
      r.orbitValue π ⟨unramifiedTwistOrbitMap νL π z.val,
        (r.orbitRegularRegion_map π z.val).mpr hz⟩ •
          Representation.IntertwiningMap.id
            (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
              (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  standardInductionComposite_eq_canonicalOrbitScalar L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi r z hz

/-- On the intersection of the original full domains, the original exact
integrals compose to every regular invariant presentation of the fraction. -/
theorem conditionalOriginalComposite_eq_canonicalOrbitScalar
    (r : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer νL π) c)
    (z : ↥(forwardFullDomainRegion χ K hK A ∩ reverseFullDomainRegion χ K hK A))
    (hz : r.denominator.val z.val ≠ 0) :
    (conditionalReverseFamily χ K hK hRefl hCST hG A ⟨z.val, z.property.2⟩).comp
      (conditionalForwardFamily χ K hK hRefl hCST hG A ⟨z.val, z.property.1⟩) =
      r.orbitValue π ⟨unramifiedTwistOrbitMap νL π z.val,
        (r.orbitRegularRegion_map π z.val).mpr hz⟩ •
          Representation.IntertwiningMap.id
            (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
              (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  standardInductionOriginalComposite_eq_canonicalOrbitScalar L hp hL
    (decomposition χ) (radical_isClosed χ) (radical_unimodular χ hG)
    (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) K hK
    (parabolic_isClosed χ) (oppositeParabolic_isClosed χ) hPK hOppK
    (projection_continuous χ) (oppositeProjection_continuous χ)
    (parameterHomeomorph χ) (normCharacters_continuous χ) A
    (forwardQuotientMeasure χ K hK) (reverseQuotientMeasure χ K hK)
    (radicalHaar χ K hK) (oppositeRadicalHaar χ K hK)
    (forwardIntersectionHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG)
    (conditionalReverseSquaredModulus χ hRefl hCST hG)
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi r z hz

end Langlands.Plancherel.DynamicOppositeCanonicalScalar
