import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

/-! # Density criteria in Hilbert spaces and in `L²` spaces of vector-valued functions

* `topologicalClosure_span_smooth_smul_eq_top`: if `span D` is dense in a normed space `E`, then
  the classes of the functions `x ↦ c(x) • h` with `c` smooth and compactly supported and
  `h ∈ D` span a dense subspace of `L^p(X, E; μ)`, for `X` a finite-dimensional real normed
  space, `1 ≤ p < ∞` and `μ` finite on compact sets.
* `PiLp.topologicalClosure_span_single_eq_top`: dense spanning sets of the factors give a dense
  spanning set of a finite `PiLp` product.
* `Submodule.topologicalClosure_span_eq_top_of_subset_closure`: transfer of density to a
  submodule seen as a space of its own.
* `subset_topologicalClosure_span_of_inner_eq`: an orthogonal-projection criterion for a
  subspace `L` of a Hilbert space to lie in the closed span of a set `S ⊆ L`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal ContDiff InnerProductSpace Topology

set_option autoImplicit false

namespace Langlands.Analysis

section IndicatorConst

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {p : ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)

/-- `indicatorConstLp` is `ℂ`-homogeneous in the constant. -/
theorem indicatorConstLp_smul (a : ℂ) (c : E) :
    indicatorConstLp p hs hμs (a • c) = a • indicatorConstLp p hs hμs c := by
  refine Lp.ext (indicatorConstLp_coeFn.trans ?_)
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)] with x hx
  rw [Pi.smul_apply, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- `indicatorConstLp` as a continuous `ℂ`-linear map in the constant. -/
def indicatorConstLpCLM [Fact (1 ≤ p)] (hp : p ≠ 0) (hp' : p ≠ ⊤) : E →L[ℂ] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := fun c => indicatorConstLp p hs hμs c
      map_add' := fun c c' => indicatorConstLp_add.symm
      map_smul' := fun a c => indicatorConstLp_smul hs hμs a c }
    (μ.real s ^ (1 / p.toReal)) fun c => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [norm_indicatorConstLp hp hp', mul_comm]

theorem indicatorConstLpCLM_apply [Fact (1 ≤ p)] (hp : p ≠ 0) (hp' : p ≠ ⊤) (c : E) :
    indicatorConstLpCLM (μ := μ) hs hμs hp hp' c = indicatorConstLp p hs hμs c :=
  rfl

/-- `indicatorConstLp` of `h` is the image of the scalar indicator under `a ↦ a • h`. -/
theorem indicatorConstLp_eq_toSpanSingleton_compLp' (h : E) :
    indicatorConstLp p hs hμs h =
      (ContinuousLinearMap.toSpanSingleton ℂ h).compLp (indicatorConstLp p hs hμs (1 : ℂ)) := by
  refine Lp.ext (indicatorConstLp_coeFn.trans ?_)
  refine EventuallyEq.trans ?_
    ((ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLp'
      (indicatorConstLp p hs hμs (1 : ℂ))).symm
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : ℂ))]
    with x hx
  rw [hx, ContinuousLinearMap.toSpanSingleton_apply]
  by_cases hxs : x ∈ s <;> simp [hxs]

end IndicatorConst

section SmoothDensity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℝ≥0∞} [hp₁ : Fact (1 ≤ p)]

/-- If `span D` is dense in `E`, then the classes in `L^p(X, E; μ)` of the functions
`x ↦ c(x) • h`, with `c : X → ℂ` smooth and compactly supported and `h ∈ D`, span a dense
subspace (`1 ≤ p < ∞`, `μ` finite on compact sets). -/
theorem topologicalClosure_span_smooth_smul_eq_top (hp : p ≠ ⊤) (D : Set E)
    (hD : (Submodule.span ℂ D).topologicalClosure = ⊤) :
    (Submodule.span ℂ {f : Lp E p μ | ∃ (c : X → ℂ) (h : E), h ∈ D ∧ HasCompactSupport c ∧
      ContDiff ℝ (⊤ : ℕ∞) c ∧ f =ᵐ[μ] fun x => c x • h}).topologicalClosure = ⊤ := by
  set S : Set (Lp E p μ) := {f | ∃ (c : X → ℂ) (h : E), h ∈ D ∧ HasCompactSupport c ∧
      ContDiff ℝ (⊤ : ℕ∞) c ∧ f =ᵐ[μ] fun x => c x • h} with hSdef
  set C := (Submodule.span ℂ S).topologicalClosure with hCdef
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp₁.out).ne'
  have hCc : IsClosed (C : Set (Lp E p μ)) := Submodule.isClosed_topologicalClosure _
  -- the indicator functions with constant values in `D`
  have hind : ∀ (h : E), h ∈ D → ∀ {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤),
      indicatorConstLp p hs hμs h ∈ C := by
    intro h hh s hs hμs
    rw [indicatorConstLp_eq_toSpanSingleton_compLp' hs hμs h]
    set T : Lp ℂ p μ →L[ℂ] Lp E p μ :=
      (ContinuousLinearMap.toSpanSingleton ℂ h).compLpL p μ with hT
    have hdense := Lp.dense_hasCompactSupport_contDiff (E := X) (F := ℂ) (μ := μ) hp
      (indicatorConstLp p hs hμs (1 : ℂ))
    have hmaps : MapsTo T {f : Lp ℂ p μ | ∃ (g : X → ℂ), f =ᵐ[μ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ (⊤ : ℕ∞) g} (C : Set (Lp E p μ)) := by
      rintro f ⟨g, hfg, hg, hg'⟩
      refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, h, hh, hg, hg', ?_⟩)
      refine ((ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLp' f).trans ?_
      filter_upwards [hfg] with x hx
      rw [ContinuousLinearMap.toSpanSingleton_apply, hx]
    have := map_mem_closure T.continuous hdense hmaps
    rwa [hCc.closure_eq] at this
  -- all indicator functions
  have hind' : ∀ (c : E) {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤),
      indicatorConstLp p hs hμs c ∈ C := by
    intro c s hs hμs
    set Φ : E →L[ℂ] Lp E p μ := indicatorConstLpCLM (μ := μ) (E := E) hs hμs hp0 hp with hΦ
    set V : Submodule ℂ E := C.comap (Φ : E →ₗ[ℂ] Lp E p μ) with hV
    have hVc : IsClosed (V : Set E) := hCc.preimage Φ.continuous
    have hDV : Submodule.span ℂ D ≤ V := Submodule.span_le.2 fun h hh => hind h hh hs hμs
    have hle : (⊤ : Submodule ℂ E) ≤ V := by
      rw [← hD]
      exact Submodule.topologicalClosure_minimal _ hDV hVc
    exact hle (Submodule.mem_top (x := c))
  rw [eq_top_iff]
  intro f _
  refine Lp.induction hp (motive := fun f => f ∈ C) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact hind' c hs hμs.ne
  · intro f g hf hg _ hfC hgC
    exact C.add_mem hfC hgC
  · exact hCc

end SmoothDensity

section PiLp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
  [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace ℂ (β i)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Dense spanning sets `S i` of the factors give the dense spanning set
`{single i x | x ∈ S i}` of `PiLp p β`. -/
theorem PiLp.topologicalClosure_span_single_eq_top (S : ∀ i, Set (β i))
    (hS : ∀ i, (Submodule.span ℂ (S i)).topologicalClosure = ⊤) :
    (Submodule.span ℂ {f : PiLp p β | ∃ i, ∃ x ∈ S i, f = PiLp.single p i x}).topologicalClosure
      = ⊤ := by
  set C := (Submodule.span ℂ {f : PiLp p β | ∃ i, ∃ x ∈ S i, f = PiLp.single p i x}).topologicalClosure
    with hCdef
  have hCc : IsClosed (C : Set (PiLp p β)) := Submodule.isClosed_topologicalClosure _
  have hsingle : ∀ i (x : β i), PiLp.single p i x ∈ C := by
    intro i x
    set Li : β i →L[ℂ] PiLp p β :=
      (PiLp.continuousLinearEquiv p ℂ β).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ β i) with hLi
    have hLi_apply : ∀ y, Li y = PiLp.single p i y := fun y => rfl
    set V : Submodule ℂ (β i) := C.comap (Li : β i →ₗ[ℂ] PiLp p β) with hV
    have hVc : IsClosed (V : Set (β i)) := hCc.preimage Li.continuous
    have hSV : Submodule.span ℂ (S i) ≤ V := Submodule.span_le.2 fun y hy => by
      show Li y ∈ C
      rw [hLi_apply]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, y, hy, rfl⟩)
    have hle : (⊤ : Submodule ℂ (β i)) ≤ V := by
      rw [← hS i]
      exact Submodule.topologicalClosure_minimal _ hSV hVc
    have := hle (Submodule.mem_top (x := x))
    simpa [V, hLi_apply] using this
  rw [eq_top_iff]
  intro f _
  have hf : f = ∑ i, PiLp.single p i (f i) := by
    ext j
    simp [Finset.sum_apply]
  rw [hf]
  exact C.sum_mem fun i _ => hsingle i (f i)

end PiLp

section Subtype

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If a submodule `L` lies in the closure of the span of the image of `T ⊆ L`, then `span T` is
dense in `L`. -/
theorem Submodule.topologicalClosure_span_eq_top_of_subset_closure (L : Submodule ℂ E)
    (T : Set L) (h : (L : Set E) ⊆ closure (Submodule.span ℂ (Subtype.val '' T) : Set E)) :
    (Submodule.span ℂ T).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have himg : Subtype.val '' (Submodule.span ℂ T : Set L) =
      (Submodule.span ℂ (Subtype.val '' T) : Set E) := by
    have := congrArg (fun W : Submodule ℂ E => (W : Set E)) (Submodule.map_span L.subtype T)
    simpa using this
  show (y : E) ∈ closure (Subtype.val '' (Submodule.span ℂ T : Set L))
  rw [himg]
  exact h y.2

/-- The span of the elements of `T` is dense in the closed span of `T`. -/
theorem Submodule.topologicalClosure_span_subtype_eq_top (T : Set E) :
    (Submodule.span ℂ {x : (Submodule.span ℂ T).topologicalClosure | (x : E) ∈ T}).topologicalClosure
      = ⊤ := by
  refine Submodule.topologicalClosure_span_eq_top_of_subset_closure _ _ ?_
  have himg : Subtype.val '' {x : (Submodule.span ℂ T).topologicalClosure | (x : E) ∈ T} = T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, Submodule.le_topologicalClosure _ (Submodule.subset_span hy)⟩, hy, rfl⟩
  rw [himg, ← Submodule.topologicalClosure_coe]

end Subtype

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Let `L` be a subspace of a Hilbert space `E`, `S ⊆ L`, and `G` a set with dense span. If for
every `g ∈ G` there is `s` in the span of `S` with `⟪Θ, s⟫ = ⟪Θ, g⟫` for all `Θ ∈ L`, then `L`
lies in the closed span of `S`. (For `Θ ∈ L`, the component of `Θ` orthogonal to the closed span
`K` of `S` is in the closure of `L`, because `K` is; by continuity it is orthogonal to `G`, hence
zero.) -/
theorem subset_topologicalClosure_span_of_inner_eq (L : Submodule ℂ E) (S : Set E)
    (hSL : S ⊆ L) (G : Set E) (hG : (Submodule.span ℂ G).topologicalClosure = ⊤)
    (h : ∀ g ∈ G, ∃ s ∈ Submodule.span ℂ S, ∀ Θ ∈ L, ⟪Θ, s⟫_ℂ = ⟪Θ, g⟫_ℂ) :
    (L : Set E) ⊆ (Submodule.span ℂ S).topologicalClosure := by
  set K := (Submodule.span ℂ S).topologicalClosure with hKdef
  have hKc : IsClosed (K : Set E) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hKc.completeSpace_coe
  -- `K` is in the closure of `L`
  have hKL : (K : Set E) ⊆ L.topologicalClosure := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    exact Submodule.span_le.2 fun x hx => Submodule.le_topologicalClosure _ (hSL hx)
  intro Θ hΘ
  set Θ' := Θ - K.starProjection Θ with hΘ'
  have hΘ'K : Θ' ∈ Kᗮ := K.sub_starProjection_mem_orthogonal Θ
  have hPK : K.starProjection Θ ∈ K := K.starProjection_apply_mem Θ
  -- `Θ'` is orthogonal to `G`
  have hG0 : ∀ g ∈ G, ⟪Θ', g⟫_ℂ = 0 := by
    intro g hg
    obtain ⟨s, hs, hsg⟩ := h g hg
    -- the identity extends to the closure of `L`
    have hcl : ∀ Ψ ∈ L.topologicalClosure, ⟪Ψ, s⟫_ℂ = ⟪Ψ, g⟫_ℂ := by
      intro Ψ hΨ
      have hclosed : IsClosed {Ψ : E | ⟪Ψ, s⟫_ℂ = ⟪Ψ, g⟫_ℂ} :=
        isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
      have hsub : (L : Set E) ⊆ {Ψ : E | ⟪Ψ, s⟫_ℂ = ⟪Ψ, g⟫_ℂ} := fun Ψ hΨ => hsg Ψ hΨ
      have := closure_minimal hsub hclosed
      rw [← Submodule.topologicalClosure_coe] at this
      exact this hΨ
    have hΘL : Θ ∈ L.topologicalClosure := Submodule.le_topologicalClosure _ hΘ
    have hsK : s ∈ K := Submodule.le_topologicalClosure _ hs
    rw [hΘ', inner_sub_left, ← hcl Θ hΘL, ← hcl _ (hKL hPK), ← inner_sub_left]
    exact Submodule.inner_left_of_mem_orthogonal hsK hΘ'K
  have hΘ'0 : Θ' = 0 := by
    have hdense : Dense (Submodule.span ℂ G : Set E) := by
      rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hG, Submodule.top_coe]
    refine hdense.eq_zero_of_inner_left ℂ fun v hv => ?_
    refine Submodule.span_induction (fun x hx => hG0 x hx) ?_ (fun x y _ _ hx hy => ?_)
      (fun a x _ hx => ?_) hv
    · exact inner_zero_right _
    · rw [inner_add_right, hx, hy, add_zero]
    · rw [inner_smul_right, hx, mul_zero]
  have : Θ = K.starProjection Θ := sub_eq_zero.1 hΘ'0
  rw [SetLike.mem_coe, this]
  exact hPK

end Orthogonal

section InnerPreserving

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']

/-- A continuous linear map that preserves inner products of elements of a set `D` with dense
span preserves all inner products. -/
theorem inner_map_map_eq_of_dense (T : H →L[ℂ] H') (D : Set H)
    (hD : (Submodule.span ℂ D).topologicalClosure = ⊤)
    (h : ∀ a ∈ D, ∀ b ∈ D, ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ) (a b : H) :
    ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ := by
  -- the set of `a` with `⟪T a, T b⟫ = ⟪a, b⟫` is a closed submodule for fixed `b`
  have key : ∀ b : H, (∀ a ∈ D, ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ) → ∀ a, ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro b hb
    let V : Submodule ℂ H :=
      { carrier := {a | ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_ofPred_eq, map_add, inner_add_left] at hx hy ⊢
          rw [hx, hy]
        zero_mem' := by simp
        smul_mem' := fun c x hx => by
          simp only [Set.mem_ofPred_eq, map_smul, inner_smul_left] at hx ⊢
          rw [hx] }
    have hVc : IsClosed (V : Set H) :=
      isClosed_eq ((T.continuous.inner continuous_const)) (continuous_id.inner continuous_const)
    have hle : (⊤ : Submodule ℂ H) ≤ V := by
      rw [← hD]
      exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hb) hVc
    exact fun a => hle (Submodule.mem_top (x := a))
  -- the set of `b` with `⟪T a, T b⟫ = ⟪a, b⟫` for all `a` is a closed submodule
  let W : Submodule ℂ H :=
    { carrier := {b | ∀ a, ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ}
      add_mem' := fun {x y} hx hy a => by
        simp only [map_add, inner_add_right]
        rw [hx a, hy a]
      zero_mem' := fun a => by simp
      smul_mem' := fun c x hx a => by
        simp only [map_smul, inner_smul_right]
        rw [hx a] }
  have hWc : IsClosed (W : Set H) := by
    have : (W : Set H) = ⋂ a, {b | ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ} := by
      ext b
      simp [W]
    rw [this]
    exact isClosed_iInter fun a =>
      isClosed_eq (continuous_const.inner T.continuous) (continuous_const.inner continuous_id)
  have hDW : Submodule.span ℂ D ≤ W :=
    Submodule.span_le.2 fun b hb => key b fun a ha => h a ha b hb
  have hle : (⊤ : Submodule ℂ H) ≤ W := by
    rw [← hD]
    exact Submodule.topologicalClosure_minimal _ hDW hWc
  exact hle (Submodule.mem_top (x := b)) a

end InnerPreserving

end Langlands.Analysis
