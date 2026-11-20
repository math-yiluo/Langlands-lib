import Langlands.Representation.Plancherel.DynamicRepresentedGalleryProduct
import Langlands.Representation.Plancherel.DynamicRepresentedIntegralNormalization

/-! # The continued opposite composite in the represented gallery -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic Haar
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicOppositeContinuedTests DynamicCommonLeviComposition
open DynamicCommonLeviStructuralComparison DynamicCommonLeviPresentationComparison
open UnramifiedOperatorFamily

attribute [local instance] equalitySubgroupMeasurable equalitySubgroupBorel

private theorem subgroupMeasureOfEq_compactOpenHaar {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    {V W : Subgroup H} (e : V = W) (hV : IsClosed (V : Set H)) (hW : IsClosed (W : Set H)) :
    subgroupMeasureOfEq e (subgroupCompactOpenHaar K hK W hW) =
      subgroupCompactOpenHaar K hK V hV := by
  subst W
  exact Measure.map_id

private theorem transport_compactOpenHaar {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    {V W : Subgroup H} (e : V = W) (hV : IsClosed (V : Set H)) (hW : IsClosed (W : Set H))
    (P : ∀ V : Subgroup H, Measure V → Prop)
    (h : P V (subgroupCompactOpenHaar K hK V hV)) :
    P W (subgroupCompactOpenHaar K hK W hW) := by
  subst W
  exact h

private theorem scalar_of_conjugate_composite {H X Y V W : Type*} [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρX : Representation ℂ H X} {ρY : Representation ℂ H Y}
    {ρV : Representation ℂ H V} {ρW : Representation ℂ H W}
    (E : ρX.Equiv ρV) (E' : ρY.Equiv ρW)
    (J : ρV.IntertwiningMap ρW) (J' : ρW.IntertwiningMap ρV) (c : ℂ)
    (h : (E.symm.toIntertwiningMap.comp (J'.comp E'.toIntertwiningMap)).comp
        (E'.symm.toIntertwiningMap.comp (J.comp E.toIntertwiningMap)) =
        c • Representation.IntertwiningMap.id ρX) :
    J'.comp J = c • Representation.IntertwiningMap.id ρV := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change J' (J v) = c • v
  apply E.symm.injective
  have hv := DFunLike.congr_fun h (E.symm v)
  change E.symm (J' (E' (E'.symm (J (E (E.symm v)))))) = c • E.symm v at hv
  rw [E.apply_symm_apply, E'.apply_symm_apply] at hv
  exact hv.trans (map_smul E.symm c v).symm

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (ha : IsSplitComponent a)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- The initial vertex is the original cocharacter. -/
abbrev oppositeGallerySource : GalleryVertex χ := ⟨χ, rfl⟩

/-- The final vertex is the literal opposite cocharacter. -/
abbrev oppositeGalleryTarget : GalleryVertex χ := (oppositeGallerySource χ).opposite

local notation "first" => oppositeGallerySource χ
local notation "last" => oppositeGalleryTarget χ
local notation "d" => galleryVertexData hG ha
local notation "hOppLevi" => Dynamic.centralizer_inverseCocharacter χ
set_option quotPrecheck false in
local notation "twisted" => (fun z : unramifiedCharacters (normCharacters χ) =>
  A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)))
local notation "intrinsic" => (fun z => SmoothRep.pullback (parameterHomeomorph χ) (twisted z))

/-- The intrinsic coefficient after twisting the literal Levi is the same
intrinsic coefficient twisted by the original actual parameter. -/
theorem intrinsicGalleryCoefficient_twist (z : unramifiedCharacters (normCharacters χ)) :
    intrinsic z = ((SmoothRep.pullback (parameterHomeomorph χ) A).twist
      z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z)) := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  have he : (intrinsic z).representation = ((SmoothRep.pullback (parameterHomeomorph χ) A).twist
      z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z)).representation := by
    apply MonoidHom.ext
    intro m
    change ((z.val ((parameterHomeomorph χ).symm ((parameterHomeomorph χ) m)) : ℂˣ) : ℂ) •
        A.representation ((parameterHomeomorph χ) m) =
      (z.val m : ℂ) • A.representation ((parameterHomeomorph χ) m)
    rw [ContinuousMulEquiv.symm_apply_apply]
  exact congrArg Rep.of he

variable
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)

local notation "JF" => forwardIntertwiner χ hRefl hCST hG K hK hPK hOppK A p
  hDForward hneForward hDForwardΩ
local notation "JR" => reverseIntertwiner χ hRefl hCST hG K hK hPK hOppK A q
  hDReverse hneReverse hDReverseΩ
local notation "μpair" => galleryPairHaar hG ha K hK

set_option maxHeartbeats 800000 in
/-- The forward endpoint gallery map agrees with the original continuation
at the fixed compact Haar scale. -/
theorem galleryIntegralOperator_eq_forward (z : p.regularRegion)
    (hPQ : representedIsPQRegular hG (d first) (d last) (intrinsic z.val)) :
    galleryIntegralOperator hG ha K hK (intrinsic z.val) first last =
      representedDynamicIntertwiner hG (d first) (d last) rfl hOppLevi (twisted z.val) (JF z) := by
  have hJ := forwardIntertwiner_isIntegral (d first) (d last) hRefl hCST hG K hK hPK hOppK A
    p hDForward hneForward hDForwardΩ z
  have hμ : representedOppositeMeasure (d last) (oppositeRadicalHaar χ K hK) = μpair first last :=
    subgroupMeasureOfEq_compactOpenHaar K hK (representedOppositeComplement_eq (d last))
      (representedComplement_isClosed (d last) (d last)) (oppositeRadical_isClosed χ)
  refine (existsUnique_representedIntegralOperator hG (d first) (d last) (d last) rfl ha
    (μpair first last) (intrinsic z.val) hPQ).unique
      (galleryIntegralOperator_spec hG ha K hK (intrinsic z.val) first last hPQ) ?_
  exact hμ ▸ hJ

set_option maxHeartbeats 900000 in
/-- The reverse endpoint gallery map agrees with the original continuation
at the same fixed compact Haar scale. -/
theorem galleryIntegralOperator_eq_reverse (z : q.regularRegion)
    (hPQ : representedIsPQRegular hG (d last) (d first) (intrinsic z.val)) :
    galleryIntegralOperator hG ha K hK (intrinsic z.val) last first =
      representedDynamicIntertwiner hG (d last) (d first) hOppLevi rfl (twisted z.val) (JR z) := by
  have hJ := reverseIntertwiner_isIntegral (d first) (d last) hRefl hCST hG K hK hPK hOppK A
    q hDReverse hneReverse hDReverseΩ z
  let W := representedOppositeComplement (d first)
  let W' := representedComplement (d (GalleryVertex.opposite last)) (d first)
  have hW : IsClosed (W : Set (rationalPoints G)) := representedComplement_isClosed (d first) (d first)
  have hW' : IsClosed (W' : Set (rationalPoints G)) := representedComplement_isClosed _ _
  have hV : W' = radical χ := by
    refine (representedComplement_eq (d (GalleryVertex.opposite last)) (d first)).trans ?_
    change radical (Dynamic.inverseCocharacter (Dynamic.inverseCocharacter χ)) ⊓ radical χ = radical χ
    rw [Dynamic.inverseCocharacter_inverseCocharacter, inf_idem]
  have he : W = W' := (representedOppositeComplement_eq (d first)).trans hV.symm
  have hμ : representedOppositeMeasure (d first) (radicalHaar χ K hK) =
      subgroupCompactOpenHaar K hK W hW :=
    subgroupMeasureOfEq_compactOpenHaar K hK (representedOppositeComplement_eq (d first))
      hW (radical_isClosed χ)
  change IsIntegralIntertwiner (d last).p (d last).l (d last).n (d last).r.isCompatible.parabolic
    (d last).radical (d last).r.isCompatible.levi (multiplication_isIso hG (d last))
    (d first).p (d first).l (d first).n (d first).r.isCompatible.parabolic
    (d first).radical (d first).r.isCompatible.levi (multiplication_isIso hG (d first))
    W (representedOppositeMeasure (d first) (radicalHaar χ K hK)) (intrinsic z.val)
    (representedDynamicIntertwiner hG (d last) (d first) hOppLevi rfl (twisted z.val) (JR z)) at hJ
  have : (μpair last first).IsHaarMeasure := galleryPairHaar_isHaarMeasure hG ha K hK last first
  refine (existsUnique_representedIntegralOperator hG (d last) (d first) (d (GalleryVertex.opposite last))
    hOppLevi ha (μpair last first) (intrinsic z.val) hPQ).unique
      (galleryIntegralOperator_spec hG ha K hK (intrinsic z.val) last first hPQ) ?_
  exact transport_compactOpenHaar K hK he hW hW'
    (fun V m => IsIntegralIntertwiner (d last).p (d last).l (d last).n (d last).r.isCompatible.parabolic
      (d last).radical (d last).r.isCompatible.levi (multiplication_isIso hG (d last))
      (d first).p (d first).l (d first).n (d first).r.isCompatible.parabolic
      (d first).radical (d first).r.isCompatible.levi (multiplication_isIso hG (d first))
      V m (intrinsic z.val)
      (representedDynamicIntertwiner hG (d last) (d first) hOppLevi rfl (twisted z.val) (JR z))) (hμ ▸ hJ)

set_option maxHeartbeats 1000000 in
/-- Any scalar computed by the represented gallery product is the scalar of
the original actual continued composite at a common regular parameter. -/
theorem actualComposite_eq_of_galleryScalar (z : ↥(p.regularRegion ∩ q.regularRegion))
    (hF : representedIsPQRegular hG (d first) (d last) (intrinsic z.val))
    (hR : representedIsPQRegular hG (d last) (d first) (intrinsic z.val))
    (c : ℂ) (h : IsGalleryCompositeScalar hG ha K hK (intrinsic z.val) first last c) :
    conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z =
      c • Representation.IntertwiningMap.id (UnramifiedLeviInduction (decomposition χ)
        (radical_isClosed χ) (leviNormCharacters χ) (parameterTransport χ z.val) A).representation := by
  let E := representedDynamicInductionEquiv hG (d first) rfl (twisted z.val)
  let E' := representedDynamicInductionEquiv hG (d last) hOppLevi (twisted z.val)
  let jf := JF ⟨z.val, z.property.1⟩
  let jr := JR ⟨z.val, z.property.2⟩
  have hf := galleryIntegralOperator_eq_forward χ hRefl hCST hG ha K hK hPK hOppK A p
    hDForward hneForward hDForwardΩ ⟨z.val, z.property.1⟩ hF
  have hr := galleryIntegralOperator_eq_reverse χ hRefl hCST hG ha K hK hPK hOppK A q
    hDReverse hneReverse hDReverseΩ ⟨z.val, z.property.2⟩ hR
  have hc := congrArg₂ (fun (u : (representedInduction hG (d last) (intrinsic z.val)).representation.IntertwiningMap
      (representedInduction hG (d first) (intrinsic z.val)).representation)
      (v : (representedInduction hG (d first) (intrinsic z.val)).representation.IntertwiningMap
        (representedInduction hG (d last) (intrinsic z.val)).representation) => u.comp v) hr hf
  exact scalar_of_conjugate_composite E E' jf jr c (hc.symm.trans h)

end Langlands.Plancherel.DynamicCommonLeviPresentations
