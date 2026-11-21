import Langlands.Representation.Plancherel.DynamicCommonLeviQuotientChart
import Langlands.Representation.Plancherel.DynamicRepresentedIntegralNormalization
import Langlands.Representation.Plancherel.ActualCommonLeviTensor

/-! # Normalization of the actual continued endpoint maps on the gallery -/

noncomputable section

universe u uV

set_option quotPrecheck false
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.HarmonicAnalysis

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviContinuation
open DynamicCommonLeviCompact DynamicCommonLeviStructuralComparison
open ActualCommonLeviTensor UnramifiedOperatorFamily StandardIntertwining

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
  equalitySubgroupMeasurable equalitySubgroupBorel
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (x y : GalleryVertex χ)

local instance continuedLeviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

set_option hygiene false in
local notation "Γ" => rationalPoints G
local notation "d" => galleryVertexData hG ha
local notation "V" => representedComplement (d x.opposite) (d y)
local notation "Q" => QuotientSpace (U := radical x.val) (radical y.val)
local notation "μV" => galleryPairHaar hG ha K hK x y
local notation "qMeasure" => pairQuotientMeasure K hK x.val y.val
local notation "h₀" => commonDecomposition χ x.val x.property
local notation "h₁" => commonDecomposition χ y.val y.property
local notation "hU₀" => radical_isClosed x.val
local notation "hU₁" => radical_isClosed y.val
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular x.val hG
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed x.val
local notation "hr₀" => commonProjection_continuous χ x.val x.property
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "L" => parameterScheme χ
local notation "e" => parameterHomeomorph χ
local notation "hν" => normCharacters_continuous χ

variable (c : GalleryQuotientChart hG ha K hK x y)

set_option maxHeartbeats 650000 in
private theorem weakIntegral_complement_at_one
    (B : SmoothRep.{0, u, uV} ℂ (levi χ))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj B)
    {Jf : Γ → B} (hJ : HasIntegral h₀ hU₀ (radical y.val) B qMeasure f Jf) :
    SmoothWeakIntegral.HasIntegral B.representation (c.scale • μV)
      (fun v : V => eval _ _ f v.val) (Jf 1) := by
  intro ℓ
  let b (q : Q) : ℂ := ℓ.val (integrand h₀ hU₀ (radical y.val) B 1 f q)
  have hb : b ∘ c.homeomorph = (fun v : V => ℓ.val (eval _ _ f v.val)) := by
    funext v
    obtain ⟨r, hr, hrv⟩ := c.representative v
    change ℓ.val (integrand h₀ hU₀ (radical y.val) B 1 f (c.homeomorph v)) = _
    rw [hr, integrand_mk, mul_one, hrv]
    rfl
  have hi : Integrable b qMeasure := (hJ 1 ℓ).1
  have he : (∫ q, b q ∂qMeasure) = ℓ.val (Jf 1) := (hJ 1 ℓ).2
  have hcomp : Integrable (b ∘ c.homeomorph) (c.scale • μV) :=
    (c.measurePreserving.integrable_comp_emb c.homeomorph.toMeasurableEquiv.measurableEmbedding).mpr hi
  exact ⟨hb ▸ hcomp, (congrArg (fun b' : V → ℂ => ∫ v, b' v ∂(c.scale • μV)) hb).symm.trans
    ((c.measurePreserving.integral_comp c.homeomorph.toMeasurableEquiv.measurableEmbedding b).trans he)⟩

variable
  (hxK : ∀ g : Γ, ∃ q : parabolic x.val, ∃ k : K, g = (q : Γ) * (k : Γ))
  (hyK : ∀ g : Γ, ∃ q : parabolic y.val, ∃ k : K, g = (q : Γ) * (k : Γ))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ContinuedPair χ hG K hK x.val x.property hxK y.val y.property hyK A)

local notation "B" => twistObject χ
local notation "E₀" => fun z => compactEquiv χ hG K hK x.val x.property hxK z A
local notation "E₁" => fun z => compactEquiv χ hG K hK y.val y.property hyK z A
local notation "I₀" => fun z => (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (B z A)
local notation "I₁" => fun z => (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj (B z A)
local notation "J" => ContinuedPair.operator χ hG K hK x.val x.property hxK y.val y.property hyK A p
local notation "C₁" => CompactInductionPicture h₁ K A
local notation "C₀" => CompactInductionPicture h₀ K A
local notation "σ" => fun z : X => SmoothRep.pullback e (B z A)
local notation "j" => (Subtype.val : V → Γ)

set_option maxHeartbeats 1200000 in
/-- The actual continuation retains the full compact-test formula on the
opposite complement at the actual quotient scale. -/
theorem continuedPair_compactTest_integral (z : p.regularRegion) (f : I₀ z.val)
    (hf : HasCompactSupport (fun v : V => eval _ _ f v.val)) (ℓ : Module.Dual ℂ A) :
    Integrable (fun v : V => ℓ (eval _ _ f v.val)) (c.scale • μV) ∧
      ℓ (eval _ _ (J z f) 1) = ∫ v : V, ℓ (eval _ _ f v.val) ∂(c.scale • μV) := by
  let f₀ : C₀ := (E₀ z.val) f
  let b := compactTestSectionValues L h₀ hU₀ hδ₀ K hP₀ hK hxK hr₀ e hν A f₀ j
  let E : C₁ →ₗ[ℂ] A := compactEvalLinear h₁ K A 1
  have he₀ : (E₀ z.val).symm f₀ = f := (E₀ z.val).symm_apply_apply f
  have hsource : (fun v : V => b v z.val) = fun v => eval _ _ f v.val :=
    funext fun v => congrArg (fun f' : I₀ z.val => eval _ _ f' v.val) he₀
  have hsupport : HasCompactSupport (fun v : V => b v z.val) := hsource.symm ▸ hf
  have start (w : p.region) : SmoothWeakIntegral.HasIntegral A.representation (c.scale • μV)
      (fun v => b v w.val) (E (restrictedCompactFamily χ hG K hK x.val x.property hxK
        y.val y.property hyK p.modulus A p.region p.converges w f₀)) := by
    let w' : pairFullDomainRegion χ K hK x.val x.property y.val A := ⟨w.val, p.converges w.property⟩
    let fw := (E₀ w.val).symm f₀
    have hJ := pairFamily_spec χ K hK x.val x.property y.val y.property p.modulus A w' fw
    have h := weakIntegral_complement_at_one hG ha K hK x y c (B w.val A) fw hJ
    exact (SmoothWeakIntegral.hasIntegral_twist_iff A.representation (c.scale • μV)
      (parameterTransport χ w.val).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ w.val))).mp h
  have hC := continuedOperator_compactTest_integral L h₀ hU₀ hδ₀ K hP₀ hK hxK hr₀ e hν A f₀ j
    (c.scale • μV) (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    p.presentation E continuous_subtype_val z.val hsupport (compactOpenCofinal_of_nonarchimedean (levi χ))
    p.isOpen_region p.nonempty_region (fun _ h => h) start z ℓ
  have hOp := ContinuedPair.operator_compact χ hG K hK x.val x.property hxK
    y.val y.property hyK A p z
  have hEval : E (p.presentation.continuedOperator z f₀) = eval _ _ (J z f) 1 := by
    calc
      _ = eval _ _ (J z ((E₀ z.val).symm f₀)) 1 :=
        (congrArg (fun R : C₀ →ₗ[ℂ] C₁ => E (R f₀)) hOp).symm
      _ = _ := congrArg (fun f' : I₀ z.val => eval _ _ (J z f') 1) he₀
  have htest : (fun v : V => ℓ (b v z.val)) = (fun v : V => ℓ (eval _ _ f v.val)) :=
    funext fun v => congrArg ℓ (congrFun hsource v)
  exact ⟨htest ▸ hC.1, (congrArg ℓ hEval.symm).trans
    (hC.2.trans (congrArg (fun g : V → ℂ => ∫ v, g v ∂(c.scale • μV)) htest))⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual continued pair conjugated through the represented induction equivalences. -/
def representedContinuedPairOperator (z : p.regularRegion) :
    (representedInduction hG (d x) (σ z.val)).representation.IntertwiningMap
      (representedInduction hG (d y) (σ z.val)).representation :=
  representedDynamicIntertwiner hG (d x) (d y) x.property y.property (B z.val A) (J z)

local notation "R" => representedContinuedPairOperator hG ha K hK x y hxK hyK A p

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The represented continuation is integral-normalized on the
boundary-vanishing subspace at the transported actual quotient measure. -/
theorem representedContinuedPair_isIntegral (z : p.regularRegion) :
    representedIsIntegralIntertwiner hG (d x) (d y) (d x.opposite)
      (c.scale • μV) (σ z.val) (R z) := by
  intro f hf ℓ
  let e₀ := representedDynamicInductionEquiv hG (d x) x.property (B z.val A)
  let e₁ := representedDynamicInductionEquiv hG (d y) y.property (B z.val A)
  obtain ⟨D, hD, hvan⟩ := (representedBoundaryVanishing_iff hG (d x) (d y) (d x.opposite)
    x.property (σ z.val) f).mp hf
  have hmem (v : V) : eval _ _ (e₀ f) v.val = eval _ _ f v.val :=
    representedDynamicInductionEquiv_eval hG (d x) x.property (B z.val A) f v.val
  have hsupport : HasCompactSupport (fun v : V => eval _ _ (e₀ f) v.val) :=
    HasCompactSupport.intro hD (fun v hv => (hmem v).trans (hvan v hv))
  obtain ⟨hi, htest⟩ := continuedPair_compactTest_integral hG ha K hK x y c hxK hyK A p z (e₀ f) hsupport ℓ
  have hout : eval _ _ (R z f) 1 = eval _ _ (J z (e₀ f)) 1 :=
    (representedDynamicInductionEquiv_eval hG (d y) y.property (B z.val A) _ 1).symm.trans
      (congrArg (fun g : I₁ z.val => eval _ _ g 1) (e₁.apply_symm_apply (J z (e₀ f))))
  have heq := funext (fun v : V => congrArg ℓ (hmem v))
  exact ⟨heq ▸ hi, (congrArg ℓ hout).trans (htest.trans
    (congrArg (fun g : V → ℂ => ∫ v, g v ∂(c.scale • μV)) heq))⟩

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original continuation is the represented gallery operator times
one positive constant on their common regular parameters. -/
def continuedPairGalleryScale :
    {s : ℝ≥0 // 0 < s ∧ ∀ (z : p.regularRegion),
      representedIsPQRegular hG (d x) (d y) (σ z.val) →
      R z = (s : ℂ) • galleryIntegralOperator hG ha K hK (σ z.val) x y} := by
  let c := galleryQuotientChart hG ha K hK x y
  let : (c.scale • μV).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul μV c.scale_pos.ne'
  refine ⟨c.scale, c.scale_pos, fun z hz => ?_⟩
  have hA := representedContinuedPair_isIntegral hG ha K hK x y c hxK hyK A p z
  have hI := galleryIntegralOperator_spec hG ha K hK (σ z.val) x y hz
  have h := representedIsIntegralIntertwiner_smul hG (d x) (d y) (d x.opposite)
    μV (σ z.val) c.scale _ hI
  exact (existsUnique_representedIntegralOperator hG (d x) (d y) (d x.opposite) x.property ha
    (c.scale • μV) (σ z.val) hz).unique hA h

end Langlands.Plancherel.DynamicCommonLeviPresentations
