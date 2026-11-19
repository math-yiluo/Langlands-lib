import Langlands.Representation.Archimedean.SmoothUnitActionDerivative

/-! # Smoothness of the actual action in the genuine smooth-vector topology -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Analysis

universe u v w

section Definition

variable {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]

/-- Continuous iterated differentials of a map of topological real vector spaces.
The differential is evaluated on a point and a tangent vector. Its correctness is
expressed by the derivative of the map along every differentiable real curve. -/
def CurveContDiffOn : (n : ℕ) → ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X],
    (X → Y) → Set X → Prop
  | 0, _, _, _, _, _, _, f, s => ContinuousOn f s
  | n + 1, X, _, _, _, _, _, f, s => ContinuousOn f s ∧ ∃ df : X × X → Y,
      (∀ (c : ℝ → X) (V : X) (t : ℝ), c t ∈ s → HasDerivAt c V t →
        HasDerivAt (f ∘ c) (df (c t, V)) t) ∧
      CurveContDiffOn n df (s ×ˢ univ)
termination_by structural n => n

end Definition

namespace CurveContDiffOn

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  {Z : Type w} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  {f : X → Y} {s : Set X}

private theorem hasDerivAt_clm_apply (L : X →L[ℝ] Y) {c : ℝ → X} {V : X} {t : ℝ}
    (hc : HasDerivAt c V t) : HasDerivAt (fun u => L (c u)) (L V) t := by
  apply hasDerivAt_iff_tendsto_slope_tvs.mpr
  refine ((L.continuous.tendsto V).comp (hasDerivAt_iff_tendsto_slope_tvs.mp hc)).congr ?_
  intro u
  simp [slope_def_module, map_sub]

private theorem hasDerivAt_prodMk {c : ℝ → Y} {e : ℝ → Z} {V : Y} {W : Z} {t : ℝ}
    (hc : HasDerivAt c V t) (he : HasDerivAt e W t) :
    HasDerivAt (fun u => (c u, e u)) (V, W) t :=
  hasDerivAt_iff_tendsto_slope_tvs.mpr
    ((hasDerivAt_iff_tendsto_slope_tvs.mp hc).prodMk_nhds (hasDerivAt_iff_tendsto_slope_tvs.mp he))

private theorem of_succ {n : ℕ} (h : CurveContDiffOn (n + 1) f s) : CurveContDiffOn n f s := by
  induction n generalizing X Y with
  | zero => exact h.1
  | succ n ih =>
      obtain ⟨hc, df, hdf, hs⟩ := h
      exact ⟨hc, df, hdf, ih hs⟩

private theorem linear (n : ℕ) (L : X →L[ℝ] Y) (s : Set X) : CurveContDiffOn n L s := by
  induction n generalizing X Y with
  | zero => exact L.continuous.continuousOn
  | succ n ih =>
      refine ⟨L.continuous.continuousOn, L.comp (ContinuousLinearMap.snd ℝ X X), ?_, ih _ _⟩
      intro c V t _ hc
      exact hasDerivAt_clm_apply L hc

private theorem prodMk {g : X → Z} {n : ℕ} (hf : CurveContDiffOn n f s)
    (hg : CurveContDiffOn n g s) : CurveContDiffOn n (fun x => (f x, g x)) s := by
  induction n generalizing X Y Z with
  | zero => exact hf.prodMk hg
  | succ n ih =>
      obtain ⟨hf, df, hd, hdf⟩ := hf
      obtain ⟨hg, dg, he, hdg⟩ := hg
      exact ⟨hf.prodMk hg, fun p => (df p, dg p),
        fun c V t hs hc => hasDerivAt_prodMk (hd c V t hs hc) (he c V t hs hc), ih hdf hdg⟩

private theorem comp_linear {W : Type w} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    {t : Set W} {n : ℕ} (hf : CurveContDiffOn n f s) (L : W →L[ℝ] X) (ht : MapsTo L t s) :
    CurveContDiffOn n (f ∘ L) t := by
  induction n generalizing W X Y with
  | zero => exact hf.comp L.continuous.continuousOn ht
  | succ n ih =>
      obtain ⟨hcont, df, hdf, hdiff⟩ := hf
      let LL := (L.comp (ContinuousLinearMap.fst ℝ W W)).prod
        (L.comp (ContinuousLinearMap.snd ℝ W W))
      refine ⟨hcont.comp L.continuous.continuousOn ht, df ∘ LL, ?_, ?_⟩
      · intro c V t' hs hc
        exact hdf (L ∘ c) (L V) t' (ht hs) (hasDerivAt_clm_apply L hc)
      · exact ih hdiff LL (fun p hp => ⟨ht hp.1, mem_univ _⟩)

private theorem comp {g : Y → Z} {t : Set Y} {n : ℕ}
    (hg : CurveContDiffOn n g t) (hf : CurveContDiffOn n f s) (ht : MapsTo f s t) :
    CurveContDiffOn n (g ∘ f) s := by
  induction n generalizing X Y Z with
  | zero => exact hg.comp hf ht
  | succ n ih =>
      have h₀ := hf.of_succ
      obtain ⟨hf, df, hd, hdf⟩ := hf
      obtain ⟨hg, dg, he, hdg⟩ := hg
      refine ⟨hg.comp hf ht, fun p => dg (f p.1, df p), ?_, ?_⟩
      · intro c V t' hs hc
        exact he (f ∘ c) (df (c t', V)) t' (ht hs) (hd c V t' hs hc)
      · have hp : CurveContDiffOn n (fun p : X × X => f p.1) (s ×ˢ univ) :=
          h₀.comp_linear (ContinuousLinearMap.fst ℝ X X) (fun _ h => h.1)
        exact ih hdg (hp.prodMk hdf) (fun p h => ⟨ht h.1, mem_univ _⟩)

private theorem add {g : X → Y} {n : ℕ} (hf : CurveContDiffOn n f s)
    (hg : CurveContDiffOn n g s) : CurveContDiffOn n (fun x => f x + g x) s :=
  (linear n ((ContinuousLinearMap.fst ℝ Y Y) + (ContinuousLinearMap.snd ℝ Y Y)) univ).comp
    (hf.prodMk hg) (mapsTo_univ _ _)

private theorem hasDerivAt_bilinear (B : X →ₗ[ℝ] Y →ₗ[ℝ] Z)
    (hB : Continuous (fun p : X × Y => B p.1 p.2)) {x : ℝ → X} {y : ℝ → Y}
    {V : X} {W : Y} {t : ℝ} (hx : HasDerivAt x V t) (hy : HasDerivAt y W t) :
    HasDerivAt (fun u => B (x u) (y u)) (B V (y t) + B (x t) W) t := by
  have hx' : Tendsto x (𝓝[≠] t) (𝓝 (x t)) :=
    hx.hasFDerivAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h₁ : Tendsto (fun u => B (slope x t u) (y t)) (𝓝[≠] t) (𝓝 (B V (y t))) :=
    (hB.tendsto (V, y t)).comp ((hasDerivAt_iff_tendsto_slope_tvs.mp hx).prodMk_nhds
      (tendsto_const_nhds (x := y t)))
  have h₂ : Tendsto (fun u => B (x u) (slope y t u)) (𝓝[≠] t) (𝓝 (B (x t) W)) :=
    (hB.tendsto (x t, W)).comp (hx'.prodMk_nhds (hasDerivAt_iff_tendsto_slope_tvs.mp hy))
  apply hasDerivAt_iff_tendsto_slope_tvs.mpr
  refine (h₁.add h₂).congr (fun u => ?_)
  let L := B.flip (y t)
  let M := B (x u)
  change L (slope x t u) + M (slope y t u) = slope (fun u => B (x u) (y u)) t u
  rw [slope_def_module, slope_def_module, slope_def_module, map_smul, map_sub, map_smul,
    map_sub, ← smul_add]
  congr 1
  change (B (x u) (y t) - B (x t) (y t)) + (B (x u) (y u) - B (x u) (y t)) = _
  abel

private theorem bilinear (B : X →ₗ[ℝ] Y →ₗ[ℝ] Z)
    (hB : Continuous (fun p : X × Y => B p.1 p.2)) (n : ℕ) (s : Set (X × Y)) :
    CurveContDiffOn n (fun p : X × Y => B p.1 p.2) s := by
  induction n generalizing s with
  | zero => exact hB.continuousOn
  | succ n ih =>
      refine ⟨hB.continuousOn, fun p => B p.2.1 p.1.2 + B p.1.1 p.2.2, ?_, ?_⟩
      · intro c V t _ hc
        exact hasDerivAt_bilinear B hB
          (hasDerivAt_clm_apply (ContinuousLinearMap.fst ℝ X Y) hc)
          (hasDerivAt_clm_apply (ContinuousLinearMap.snd ℝ X Y) hc)
      · let fst := ContinuousLinearMap.fst ℝ (X × Y) (X × Y)
        let snd := ContinuousLinearMap.snd ℝ (X × Y) (X × Y)
        let p₁ := ((ContinuousLinearMap.fst ℝ X Y).comp snd).prod
          ((ContinuousLinearMap.snd ℝ X Y).comp fst)
        let p₂ := ((ContinuousLinearMap.fst ℝ X Y).comp fst).prod
          ((ContinuousLinearMap.snd ℝ X Y).comp snd)
        exact ((ih univ).comp (linear n p₁ _) (mapsTo_univ _ _)).add
          ((ih univ).comp (linear n p₂ _) (mapsTo_univ _ _))

private theorem of_contDiffOn {B : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {C : Type v} [NormedAddCommGroup C] [NormedSpace ℝ C] {g : B → C} {s : Set B}
    (hs : IsOpen s) (hg : ContDiffOn ℝ ∞ g s) (n : ℕ) : CurveContDiffOn n g s := by
  induction n generalizing B C with
  | zero => exact hg.continuousOn
  | succ n ih =>
      let df := fderivWithin ℝ g s
      refine ⟨hg.continuousOn, fun p : B × B => df p.1 p.2, ?_, ?_⟩
      · intro c V t hst hc
        exact ((hg.differentiableOn (by simp) _ hst).hasFDerivWithinAt.hasFDerivAt
          (hs.mem_nhds hst)).comp_hasDerivAt t hc
      · have hd : ContDiffOn ℝ ∞ df s := hg.fderivWithin hs.uniqueDiffOn (by simp)
        apply ih (hs.prod isOpen_univ)
        exact (hd.comp contDiffOn_fst (fun _ h => h.1)).clm_apply contDiffOn_snd

end CurveContDiffOn
end Langlands.Analysis

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.Analysis

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "U" => Set.range (Units.val : Aˣ → A)

private def operatorBilinear : A →ₗ[ℝ] D →ₗ[ℝ] D where
  toFun X := (operator 𝓜 R X).restrictScalars ℝ
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply (toSmooth 𝓜 R).injective
    change smoothLieDerivativeDirection 𝓜 R (X + Y) (toSmooth 𝓜 R v) =
      (smoothLieDerivativeDirection 𝓜 R X + smoothLieDerivativeDirection 𝓜 R Y)
        (toSmooth 𝓜 R v)
    rw [map_add]
  map_smul' c X := by
    apply LinearMap.ext
    intro v
    apply (toSmooth 𝓜 R).injective
    change smoothLieDerivativeDirection 𝓜 R (c • X) (toSmooth 𝓜 R v) =
      (c • smoothLieDerivativeDirection 𝓜 R X) (toSmooth 𝓜 R v)
    rw [map_smul]

/-- The genuine action on smooth vectors has continuous iterated differentials of every
order in the open units chart. The underlying topology is the word-derivative topology. -/
theorem curveContDiffOn_unitsChartAction (hR : IsContinuousRepresentation R) (n : ℕ) :
    CurveContDiffOn n (unitsChartAction R) (U ×ˢ (univ : Set D)) := by
  let s := U ×ˢ (univ : Set D)
  let T := (A × D) × (A × D)
  have hcont := continuousOn_unitsChartAction R hR
  induction n with
  | zero => exact hcont
  | succ n ih =>
      let p₁ := ContinuousLinearMap.fst ℝ (A × D) (A × D)
      let p₂ := ContinuousLinearMap.snd ℝ (A × D) (A × D)
      let x := (ContinuousLinearMap.fst ℝ A D).comp p₁
      let v := (ContinuousLinearMap.snd ℝ A D).comp p₁
      let Y := (ContinuousLinearMap.fst ℝ A D).comp p₂
      let W := (ContinuousLinearMap.snd ℝ A D).comp p₂
      let J := fun p : T => (x p, operator 𝓜 R ((Ring.inverse (x p)) * Y p) (v p) + W p)
      refine ⟨hcont, unitsChartAction R ∘ J, ?_, ?_⟩
      · intro c V t ht hc
        obtain ⟨g, hg⟩ := ht.1
        have hc₁ := CurveContDiffOn.hasDerivAt_clm_apply (ContinuousLinearMap.fst ℝ A D) hc
        have hc₂ := CurveContDiffOn.hasDerivAt_clm_apply (ContinuousLinearMap.snd ℝ A D) hc
        have hd := hasDerivAt_unitsChartAction R hR g hc₁ hg.symm hc₂
        change HasDerivAt _ (unitsChartAction R
          ((c t).1, operator 𝓜 R ((Ring.inverse (c t).1) * V.1) (c t).2 + V.2)) t
        rw [← hg, unitsChartAction_val, Ring.inverse_unit]
        exact hd
      · have hinv : ContDiffOn ℝ ∞ (Ring.inverse : A → A) U := by
          rintro x ⟨g, rfl⟩
          exact (contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) g).contDiffWithinAt
        have hx : CurveContDiffOn n x (s ×ˢ (univ : Set (A × D))) :=
          CurveContDiffOn.linear n x _
        have hxi : CurveContDiffOn n (fun p : T => Ring.inverse (x p)) (s ×ˢ univ) :=
          (CurveContDiffOn.of_contDiffOn Units.isOpenEmbedding_val.isOpen_range hinv n).comp
            hx (fun _ h => h.1.1)
        have hm : CurveContDiffOn n (fun p : T => Ring.inverse (x p) * Y p) (s ×ˢ univ) :=
          (CurveContDiffOn.of_contDiffOn isOpen_univ
            (show ContDiffOn ℝ ∞ (fun p : A × A => p.1 * p.2) univ from contDiff_mul.contDiffOn)
            n).comp (hxi.prodMk (CurveContDiffOn.linear n Y _)) (mapsTo_univ _ _)
        have hop := (CurveContDiffOn.bilinear (operatorBilinear R)
          (continuous_operator_uncurry R) n univ).comp
            (hm.prodMk (CurveContDiffOn.linear n v _)) (mapsTo_univ _ _)
        have hJ : CurveContDiffOn n J (s ×ˢ univ) :=
          hx.prodMk (hop.add (CurveContDiffOn.linear n W _))
        exact ih.comp hJ (fun p hp => ⟨hp.1.1, mem_univ _⟩)

end Langlands.Archimedean.DerivativeSmoothVectors
