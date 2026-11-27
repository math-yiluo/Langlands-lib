import Langlands.Global.RankinSelberg.RealParabolicTraceLevi
import Langlands.Representation.Archimedean.SmoothDerivativeOpenMapping

/-! # Factorization of the compact real parabolic trace -/

noncomputable section

open Set TopologicalSpace
open scoped Distributions Manifold Matrix.Norms.Operator Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealStandardCompactBanach RealExactWhittakerUniqueness DerivativeSmoothVectors
open Langlands.Shahidi (blockWeyl swapRank)

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "S" => realStandardModule
local notation:max "D" d:max ds:max => DerivativeSmoothVectors (matrixModel ℝ d) (representation (n := d) ds)
local notation:max "act" d:max ds:max => DerivativeSmoothVectors.representation (matrixModel ℝ d)
  (representation (n := d) ds)

private def standardEvaluation {d : ℕ} (ds : List RealBlock) (u : G d) : D d ds →L[ℂ] ℂ :=
  (profileEval ds 1).comp ((representation ds u).comp (derivativeCLM _ _ []))

private theorem standardEvaluation_apply {d : ℕ} (ds : List RealBlock) (u : G d) (v : D d ds) :
    standardEvaluation ds u v = ((derivativeEquiv ds).symm v).val u := by
  obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
  simp only [standardEvaluation, ContinuousLinearMap.comp_apply, derivativeCLM_apply,
    iteratedLieDerivative_nil, toSmooth_derivativeEquiv, profileEval_one_orbit, embed_val,
    extensionOfProfile_restriction, LinearEquiv.symm_apply_apply]

private theorem standardEvaluation_ext {d : ℕ} (ds : List RealBlock) {v w : D d ds}
    (h : ∀ u : G d, standardEvaluation ds u v = standardEvaluation ds u w) : v = w := by
  apply (derivativeEquiv ds).symm.injective
  apply Subtype.ext
  funext u
  simpa only [standardEvaluation_apply] using h u

private theorem continuous_of_closed_graph {d e : ℕ} (ds es : List RealBlock)
    (T : D d ds →ₗ[ℂ] D e es) (hT : IsClosed (T.graph : Set (D d ds × D e es))) :
    Continuous T := by
  let E := D d ds
  let F := D e es
  let W := T.graph
  let : MetrizableSpace E := metrizableSpace_of_finiteDimensional _ _
  let : MetrizableSpace F := metrizableSpace_of_finiteDimensional _ _
  let : FirstCountableTopology E := inferInstance
  let : FirstCountableTopology F := inferInstance
  let : FirstCountableTopology W := Subtype.firstCountableTopology (W : Set (E × F))
  let : CompleteSpace E := completeSpace_of_isContinuousRepresentation_units _
    (isContinuousRepresentation ds)
  let : CompleteSpace F := completeSpace_of_isContinuousRepresentation_units _
    (isContinuousRepresentation es)
  let : IsUniformAddGroup W := W.toAddSubgroup.isUniformAddGroup
  let : ContinuousSMul ℝ W := continuousSMul_induced (W.subtype.restrictScalars ℝ)
  let : LocallyConvexSpace ℝ W := LocallyConvexSpace.induced (W.subtype.restrictScalars ℝ)
  let : CompleteSpace W := hT.isComplete.completeSpace_coe
  let : (𝓤 E).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : BaireSpace E := inferInstance
  let p : W →L[ℂ] E := (ContinuousLinearMap.fst ℂ E F).comp W.subtypeL
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      have hx := (T.mem_graph_iff x.val).mp x.property
      have hy := (T.mem_graph_iff y.val).mp y.property
      have h : x.val.1 = y.val.1 := hxy
      exact Subtype.ext (Prod.ext h (hx.trans ((congrArg T h).trans hy.symm)))
    · intro x
      exact ⟨⟨(x, T x), (T.mem_graph_iff _).mpr rfl⟩, rfl⟩
  have hpOpen : IsOpenMap p := Langlands.Analysis.frechetOpenMapping _ _ (p.restrictScalars ℝ) hp.2
  let b : W ≃ E := Equiv.ofBijective p hp
  have hInv : Continuous b.symm := b.continuous_symm_iff.mpr hpOpen
  have heq (x : E) : (b.symm x).val.2 = T x := by
    rw [(T.mem_graph_iff _).mp (b.symm x).property]
    exact congrArg T (b.apply_symm_apply x)
  exact (continuous_snd.comp (continuous_subtype_val.comp hInv)).congr heq

/-- An algebraic section is continuous when each of its evaluations is a fixed multiple of an
input evaluation. The separating family of evaluations makes its graph closed. -/
private theorem exists_continuous_of_eval_mul {d e : ℕ} (ds es : List RealBlock)
    (F : D d ds → D e es)
    (hF : ∀ u : G e, ∃ (v : G d) (c : ℂ), ∀ x, standardEvaluation es u (F x) =
      c * standardEvaluation ds v x) :
    ∃ T : D d ds →L[ℂ] D e es, ∀ x, T x = F x := by
  let T : D d ds →ₗ[ℂ] D e es :=
    { toFun := F
      map_add' := fun x y => standardEvaluation_ext es fun u => by
        obtain ⟨v, c, h⟩ := hF u
        rw [map_add, h, h, h, map_add, mul_add]
      map_smul' := fun z x => standardEvaluation_ext es fun u => by
        obtain ⟨v, c, h⟩ := hF u
        rw [map_smul, h, h, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]
        rfl }
  refine ⟨⟨T, continuous_of_closed_graph ds es T ?_⟩, fun _ => rfl⟩
  have hgraph : (T.graph : Set (D d ds × D e es)) =
      ⋂ u : G e, {p | standardEvaluation es u p.2 = standardEvaluation es u (F p.1)} := by
    ext p
    change p ∈ T.graph ↔ _
    rw [T.mem_graph_iff, mem_iInter]
    change p.2 = F p.1 ↔ ∀ u : G e,
      standardEvaluation es u p.2 = standardEvaluation es u (F p.1)
    exact ⟨fun h u => congrArg (standardEvaluation es u) h, standardEvaluation_ext es⟩
  rw [hgraph]
  apply isClosed_iInter
  intro u
  obtain ⟨v, c, h⟩ := hF u
  simp_rw [h]
  exact isClosed_eq ((standardEvaluation es u).continuous.comp continuous_snd)
    (continuous_const.mul ((standardEvaluation ds v).continuous.comp continuous_fst))

variable {m p : ℕ} {d₁ d₂ : List RealBlock}

local notation "m₁" => m + 1
local notation "m₂" => p + 1
local notation "N" => (p + 1 + m) + 1
local notation "X" => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => 𝓓((⊤ : Opens X), ℂ)

private theorem standardEvaluation_smoothSectionVector
    (hm : realRank d₁ = m₁) (hp : realRank d₂ = m₂) (f : S m₁ d₁) (g : S m₂ d₂) (φ : Test)
    (u : G N) : standardEvaluation (d₂ ++ d₁) u (smoothSectionVector hm hp f g φ) =
      standardSection f.val g.val φ u := by
  rw [standardEvaluation_apply]
  simpa only [map_one, Module.End.one_apply, mul_one] using
    reconstruct_translate_smoothSectionVector hm hp f g φ 1 u

private theorem standardSection_eval_mul (φ : Test) (u : G N) :
    ∃ (A : G m₁) (B : G m₂) (c : ℂ), ∀ (f : S m₁ d₁) (g : S m₂ d₂),
      standardSection f.val g.val φ u = c * f.val A * g.val B := by
  let v := blockWeyl m₁ m₂ ℝ * swapRank m₁ m₂ ℝ u
  by_cases hv : v ∈ parabolicCell m₁ m₂
  · obtain ⟨A, B, C, Y, hv⟩ := exists_cellCoordinates v hv
    refine ⟨A, B, detWeight (-((m₂ : ℕ) : ℂ) / 2) A.val * detWeight (((m₁ : ℕ) : ℂ) / 2) B.val * φ Y,
      fun f g => ?_⟩
    unfold standardSection
    rw [(realParabolicCompactSection m₁ m₂ _ _ f.val g.val φ f.2.1.1 g.2.1.1
      φ.contDiff φ.hasCompactSupport).2.2 v A B C Y hv]
    ring
  · refine ⟨1, 1, 0, fun f g => ?_⟩
    simp [standardSection, compactSection, ← show v = blockWeyl m₁ m₂ ℝ * swapRank m₁ m₂ ℝ u from rfl, hv]

private theorem exists_smoothSection_left
    (hm : realRank d₁ = m₁) (hp : realRank d₂ = m₂) (g : S m₂ d₂) (φ : Test) :
    ∃ T : D m₁ d₁ →L[ℂ] D N (d₂ ++ d₁), ∀ f : S m₁ d₁,
      T (derivativeEquiv d₁ f) = smoothSectionVector hm hp f g φ := by
  obtain ⟨T, hT⟩ := exists_continuous_of_eval_mul d₁ (d₂ ++ d₁)
    (fun v => smoothSectionVector hm hp ((derivativeEquiv d₁).symm v) g φ) (fun u => by
      obtain ⟨A, B, c, h⟩ := standardSection_eval_mul (d₁ := d₁) (d₂ := d₂) φ u
      refine ⟨A, c * g.val B, fun v => ?_⟩
      rw [standardEvaluation_smoothSectionVector, h, standardEvaluation_apply]
      ring)
  exact ⟨T, fun f => by rw [hT, LinearEquiv.symm_apply_apply]⟩

private theorem exists_smoothSection_right
    (hm : realRank d₁ = m₁) (hp : realRank d₂ = m₂) (f : S m₁ d₁) (φ : Test) :
    ∃ T : D m₂ d₂ →L[ℂ] D N (d₂ ++ d₁), ∀ g : S m₂ d₂,
      T (derivativeEquiv d₂ g) = smoothSectionVector hm hp f g φ := by
  obtain ⟨T, hT⟩ := exists_continuous_of_eval_mul d₂ (d₂ ++ d₁)
    (fun v => smoothSectionVector hm hp f ((derivativeEquiv d₂).symm v) φ) (fun u => by
      obtain ⟨A, B, c, h⟩ := standardSection_eval_mul (d₁ := d₁) (d₂ := d₂) φ u
      exact ⟨B, c * f.val A, fun v => by
        rw [standardEvaluation_smoothSectionVector, h, standardEvaluation_apply]⟩)
  exact ⟨T, fun g => by rw [hT, LinearEquiv.symm_apply_apply]⟩

private theorem whittakerCharacter_one (r : ℕ) (a : ℝˣ) :
    realWhittakerCharacter a (1 : G (r + 1)) = 1 := by
  have h : (∑ i : Fin r, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i.castSucc i.succ) = 0 :=
    Finset.sum_eq_zero fun i _ => Matrix.one_apply_ne (ne_of_lt (Fin.castSucc_lt_succ (i := i)))
  simp [realWhittakerCharacter, h]

private theorem translate_one {d : ℕ} (ds : List RealBlock) (f : S d ds) : translate ds 1 f = f :=
  Subtype.ext (funext fun u => by rw [translate_apply, mul_one])

private theorem trace_left_isWhittaker (hm : realRank d₁ = m₁) (hp : realRank d₂ = m₂)
    (g : S m₂ d₂) (a : ℝˣ) (L : D N (d₂ ++ d₁) →L[ℂ] ℂ)
    (hL : IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L)
    (τ : Test) (hτ : transverseMoment a τ = 1) :
    ∃ T : D m₁ d₁ →L[ℂ] ℂ, IsSmoothWhittakerEvaluation d₁ a T ∧
      ∀ f : S m₁ d₁, T (derivativeEquiv d₁ f) = transverseTraceCoefficient hm hp f g L τ := by
  obtain ⟨T, hT⟩ := exists_smoothSection_left hm hp g τ
  refine ⟨L.comp T, ?_, fun f => congrArg L (hT f)⟩
  intro u v
  obtain ⟨f, rfl⟩ := (derivativeEquiv d₁).surjective v
  simp only [← derivativeEquiv_translate, ContinuousLinearMap.comp_apply, hT]
  have h := realParabolicTraceLevi m p d₁ d₂ hm hp f g a L hL τ hτ u 1
  simpa only [Subgroup.coe_one, translate_one, whittakerCharacter_one, mul_one,
    transverseTraceCoefficient] using h

private theorem trace_right_isWhittaker (hm : realRank d₁ = m₁) (hp : realRank d₂ = m₂)
    (f : S m₁ d₁) (a : ℝˣ) (L : D N (d₂ ++ d₁) →L[ℂ] ℂ)
    (hL : IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L)
    (τ : Test) (hτ : transverseMoment a τ = 1) :
    ∃ T : D m₂ d₂ →L[ℂ] ℂ, IsSmoothWhittakerEvaluation d₂ a T ∧
      ∀ g : S m₂ d₂, T (derivativeEquiv d₂ g) = transverseTraceCoefficient hm hp f g L τ := by
  obtain ⟨T, hT⟩ := exists_smoothSection_right hm hp f τ
  refine ⟨L.comp T, ?_, fun g => congrArg L (hT g)⟩
  intro u v
  obtain ⟨g, rfl⟩ := (derivativeEquiv d₂).surjective v
  simp only [← derivativeEquiv_translate, ContinuousLinearMap.comp_apply, hT]
  have h := realParabolicTraceLevi m p d₁ d₂ hm hp f g a L hL τ hτ 1 u
  simpa only [Subgroup.coe_one, translate_one, whittakerCharacter_one, one_mul,
    transverseTraceCoefficient] using h

/-- The restriction to compact parabolic sections is the product of the two Levi
Whittaker functionals and the transverse Fourier moment, up to one scalar. -/
def RealParabolicTraceProductStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
    (a : ℝˣ) (L : D (p + 1 + m + 1) (d₂ ++ d₁) →L[ℂ] ℂ)
    (L₁ : D (m + 1) d₁ →L[ℂ] ℂ) (L₂ : D (p + 1) d₂ →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L →
    IsSmoothWhittakerEvaluation d₁ a L₁ → IsSmoothWhittakerEvaluation d₂ a L₂ →
    L₁ ≠ 0 → L₂ ≠ 0 → ∃ c : ℂ, ∀ (f : S (m + 1) d₁) (g : S (p + 1) d₂)
      (φ : 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)), ℂ)),
      L (smoothSectionVector hm hp f g φ) = c * L₁ (derivativeEquiv d₁ f) *
        L₂ (derivativeEquiv d₂ g) * transverseMoment a φ

set_option maxHeartbeats 650000 in
theorem realParabolicTraceProduct : RealParabolicTraceProductStatement := by
  intro m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hL₁ne hL₂ne
  obtain ⟨τ, hτ⟩ := exists_transverseMoment_eq_one (m := m) (p := p) a
  let B := fun (f : S (m + 1) d₁) (g : S (p + 1) d₂) => transverseTraceCoefficient hm hp f g L τ
  have hex : ∃ v, L₁ v ≠ 0 := by
    by_contra! h
    apply hL₁ne
    exact ContinuousLinearMap.ext h
  obtain ⟨v, hv⟩ := hex
  let f₀ := (derivativeEquiv d₁).symm ((L₁ v)⁻¹ • v)
  have hf₀ : L₁ (derivativeEquiv d₁ f₀) = 1 := by
    dsimp only [f₀]
    rw [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  have hleft (f : S (m + 1) d₁) (g : S (p + 1) d₂) : B f g = B f₀ g * L₁ (derivativeEquiv d₁ f) := by
    obtain ⟨T, hT, hv⟩ := trace_left_isWhittaker hm hp g a L hL τ hτ
    obtain ⟨c, hc⟩ := exists_smul_of_smoothEvaluation d₁ hm a L₁ T hL₁ hT hL₁ne
    have h' (f' : S (m + 1) d₁) : B f' g = c * L₁ (derivativeEquiv d₁ f') := by
      rw [show B f' g = T (derivativeEquiv d₁ f') from (hv f').symm, hc]
      rfl
    rw [h' f₀, hf₀, mul_one]
    exact h' f
  obtain ⟨T, hT, hv⟩ := trace_right_isWhittaker hm hp f₀ a L hL τ hτ
  obtain ⟨c, hc⟩ := exists_smul_of_smoothEvaluation d₂ hp a L₂ T hL₂ hT hL₂ne
  refine ⟨c, fun f g φ => ?_⟩
  have h' : B f₀ g = c * L₂ (derivativeEquiv d₂ g) := by
    rw [show B f₀ g = T (derivativeEquiv d₂ g) from (hv g).symm, hc]
    rfl
  rw [eval_eq_transverseTraceCoefficient hm hp f g a L hL τ hτ]
  change B f g * transverseMoment a φ = _
  rw [hleft, h']
  ring

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
