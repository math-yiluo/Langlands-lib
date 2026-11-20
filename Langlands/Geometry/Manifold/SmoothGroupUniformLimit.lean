import Langlands.Geometry.Manifold.SmoothGroupChartDerivative
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Locally uniform limits of invariant derivatives -/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
  {ι A : Type*} {l : Filter ι} [l.NeBot]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "J" => Fin (Module.finrank ℝ E)

variable {f : ι → A → G → ℂ} {g : A → G → ℂ}

/-- Assemble a coordinate derivative from scalar values in an invariant frame. -/
def invariantCoordinateDerivative {ι' : Type*} [Fintype ι']
    (L : ι' → E →L[ℝ] ℝ) (d : ι' → ℂ) : E →L[ℝ] ℂ :=
  ∑ j, (L j).smulRight (d j)

private theorem exists_chartDerivativeLimits
    (step : GroupLieAlgebra 𝓘E G → A → A)
    (hs : ∀ i a, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (f i a))
    (hder : ∀ i a X, groupDirectionalValue 𝓘E X (f i a) = f i (step X a))
    (hlim : ∀ a, TendstoLocallyUniformly (fun i => f i a) (g a) l)
    (ψ : E → G) {S : Set E} (hS : IsOpen S)
    (hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ S) :
    ∃ (X : J → GroupLieAlgebra 𝓘E G) (L : J → E → E →L[ℝ] ℝ),
      (∀ j, ContDiffOn ℝ ∞ (L j) S) ∧
      ∀ a : A,
        let D : E → E →L[ℝ] ℂ := fun x =>
          invariantCoordinateDerivative (fun j => L j x) (fun j => g (step (X j) a) (ψ x))
        TendstoLocallyUniformlyOn (fun i => fderiv ℝ (f i a ∘ ψ)) D l S ∧
          ∀ x ∈ S, HasFDerivAt (g a ∘ ψ) (D x) x := by
  obtain ⟨X, L, hL, hexp⟩ := exists_invariantDerivativeExpansion ψ hS hψ
  refine ⟨X, L, hL, fun a => ?_⟩
  let D (x : E) : E →L[ℝ] ℂ :=
    invariantCoordinateDerivative (fun j => L j x) (fun j => g (step (X j) a) (ψ x))
  let DF (i : ι) (x : E) : E →L[ℝ] ℂ :=
    invariantCoordinateDerivative (fun j => L j x) (fun j => f i (step (X j) a) (ψ x))
  have hF (i : ι) (x : E) (hx : x ∈ S) : HasFDerivAt (f i a ∘ ψ) (DF i x) x := by
    simpa only [DF, invariantCoordinateDerivative, hder] using hexp (f i a) (hs i a) x hx
  have hc (a₀ : A) : TendstoLocallyUniformlyOn (fun i => f i a₀ ∘ ψ) (g a₀ ∘ ψ) l S :=
    (tendstoLocallyUniformlyOn_univ.mpr (hlim a₀)).comp ψ (mapsTo_univ _ _) hψ.continuousOn
  have hDF : TendstoLocallyUniformlyOn DF D l S := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro x hx
    rw [tendstoUniformlyOnFilter_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
      tendsto_comap_iff]
    let t := l ×ˢ 𝓝[S] x
    have hfc (j : J) : Tendsto (fun p : ι × E =>
        -g (step (X j) a) (ψ p.2) + f p.1 (step (X j) a) (ψ p.2)) t (𝓝 0) := by
      have hp := tendstoLocallyUniformlyOn_iff_filter.mp (hc (step (X j) a)) x hx
      rwa [tendstoUniformlyOnFilter_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
        tendsto_comap_iff] at hp
    have hLC (j : J) : Tendsto (fun p : ι × E => L j p.2) t (𝓝 (L j x)) :=
      (show Tendsto (L j) (𝓝[S] x) (𝓝 (L j x)) from (hL j).continuousOn x hx).comp tendsto_snd
    have hsmul (c : E →L[ℝ] ℝ) (v : ℂ) :
        ContinuousLinearMap.smulRightL ℝ E ℂ c v = c.smulRight v := rfl
    have hSum : Tendsto (fun p : ι × E => ∑ j, (L j p.2).smulRight
        (-g (step (X j) a) (ψ p.2) + f p.1 (step (X j) a) (ψ p.2))) t (𝓝 0) := by
      have hj (j : J) :=
        ((ContinuousLinearMap.smulRightL ℝ E ℂ).isBoundedBilinearMap.continuous.tendsto
          (L j x, 0)).comp ((hLC j).prodMk_nhds (hfc j))
      simpa only [Function.comp_def, hsmul, ContinuousLinearMap.smulRight_zero,
        Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hj j)
    simpa only [Function.comp_def, DF, D, invariantCoordinateDerivative, ← hsmul,
      map_add, map_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib] using hSum
  refine ⟨?_, fun x hx =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn hS hDF hF
      (fun y hy => (hc a).tendsto_at hy) hx⟩
  exact hDF.congr (fun i x hx => (hF i x hx).fderiv.symm)

/-- A locally uniform limit of smooth functions and all their invariant
derivatives is smooth, and the limiting derivatives are its actual derivatives.
The index transition records which member differentiates a given member. -/
theorem contMDiff_of_tendstoLocallyUniformly_invariantDerivatives
    (step : GroupLieAlgebra 𝓘E G → A → A)
    (hs : ∀ i a, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (f i a))
    (hder : ∀ i a X, groupDirectionalValue 𝓘E X (f i a) = f i (step X a))
    (hlim : ∀ a, TendstoLocallyUniformly (fun i => f i a) (g a) l) :
    (∀ a, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (g a)) ∧
      ∀ a X, groupDirectionalValue 𝓘E X (g a) = g (step X a) := by
  have hCD (n : ℕ) {S : Set E} (hS : IsOpen S) (ψ : E → G)
      (hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ S) :
      ∀ a, ContDiffOn ℝ n (g a ∘ ψ) S := by
    induction n with
    | zero =>
      intro a
      rw [Nat.cast_zero, contDiffOn_zero]
      refine ((tendstoLocallyUniformlyOn_univ.mpr (hlim a)).comp ψ (mapsTo_univ _ _)
        hψ.continuousOn).continuousOn ?_
      exact Frequently.of_forall fun i => (hs i a).continuous.comp_continuousOn hψ.continuousOn
    | succ n ih =>
      intro a
      obtain ⟨X, L, hL, hD⟩ :=
        exists_chartDerivativeLimits (f := f) (g := g) (l := l) step hs hder hlim ψ hS hψ
      let D (x : E) : E →L[ℝ] ℂ := ∑ j, (L j x).smulRight (g (step (X j) a) (ψ x))
      rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn]
      refine ⟨fun h => ((show (n : ℕ∞ω) ≠ ω by simp) h).elim, D, ?_, fun x hx =>
        ((hD a).2 x hx).hasFDerivWithinAt⟩
      apply ContDiffOn.sum
      intro j _
      exact ((hL j).of_le (by simp)).smulRight (ih (step (X j) a))
  have hg (a : A) : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (g a) := by
    intro x
    let e := extChartAt 𝓘E x
    have hx : e x ∈ e.target := e.map_source (mem_extChartAt_source x)
    rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ,
      contMDiffAt_iff_contDiffAt]
    refine (contDiffOn_infty.mpr (fun n => hCD n (isOpen_extChartAt_target (I := 𝓘E) x)
      e.symm (contMDiffOn_extChartAt_symm x) a) (e x) hx).contDiffAt ?_
    exact (isOpen_extChartAt_target (I := 𝓘E) x).mem_nhds hx
  refine ⟨hg, fun a X => ?_⟩
  funext x
  let e := extChartAt 𝓘E (1 : G)
  let ψ (y : E) := x * e.symm y
  have hS : IsOpen e.target := isOpen_extChartAt_target (I := 𝓘E) (1 : G)
  have he : e 1 ∈ e.target := e.map_source (mem_extChartAt_source (1 : G))
  have he₁ : e.symm (e 1) = 1 := e.left_inv (mem_extChartAt_source (1 : G))
  have hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ e.target :=
    contMDiffOn_const.mul (contMDiffOn_extChartAt_symm (1 : G))
  obtain ⟨Y, L, _hL, hD⟩ :=
    exists_chartDerivativeLimits (f := f) (g := g) (l := l) step hs hder hlim ψ hS hψ
  have htrans (u : G → ℂ) (hu : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ u) :
      fderiv ℝ (u ∘ ψ) (e 1) X = groupDirectionalValue 𝓘E X u x := by
    let v (y : G) := u (x * y)
    have hv : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ v := hu.comp (contMDiff_const.mul contMDiff_id)
    have hMD : MDifferentiableAt 𝓘E 𝓘E (e.symm : E → G) (e 1) :=
      ((contMDiffOn_extChartAt_symm (I := 𝓘E) (n := ∞) (1 : G) (e 1) he).contMDiffAt
        (hS.mem_nhds he)).mdifferentiableAt (by simp)
    change fderiv ℝ (v ∘ e.symm) (e 1) X = mvfderiv 𝓘E v 1 X
    have hc := mvfderiv_comp_apply_of_eq (I := 𝓘E) (I' := 𝓘E) (e 1)
      (hv.mdifferentiableAt (by simp)) hMD he₁ (X : TangentSpace 𝓘E (e 1))
    have hide := mfderivWithin_range_extChartAt_symm (I := 𝓘E) (x := (1 : G))
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hide
    have hide' : mfderiv 𝓘E 𝓘E (e.symm : E → G) (e 1) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘E (e 1)) := hide
    rw [hide'] at hc
    change mvfderiv 𝓘E (v ∘ e.symm) (e 1) X = mvfderiv 𝓘E v 1 X at hc
    rw [← mvfderiv_eq_fderiv]
    exact hc
  have hfAt (i : ι) : fderiv ℝ (f i a ∘ ψ) (e 1) X = f i (step X a) x :=
    (htrans (f i a) (hs i a)).trans (congrFun (hder i a X) x)
  have ht := (hD a).1.tendsto_at he
  have htX := ((ContinuousLinearMap.apply (E := E) ℝ ℂ X).continuous.tendsto _).comp ht
  have hDx := ((hD a).2 (e 1) he).fderiv
  have htarget : (∑ j, (L j (e 1)).smulRight (g (step (Y j) a) (ψ (e 1)))) (X : E) =
      groupDirectionalValue 𝓘E X (g a) x :=
    (congrArg (fun D : E →L[ℝ] ℂ => D X) hDx.symm).trans (htrans (g a) (hg a))
  change Tendsto (fun i => fderiv ℝ (f i a ∘ ψ) (e 1) X) l
    (𝓝 ((∑ j, (L j (e 1)).smulRight (g (step (Y j) a) (ψ (e 1)))) X)) at htX
  rw [funext hfAt, htarget] at htX
  exact tendsto_nhds_unique htX
    ((tendstoLocallyUniformlyOn_univ.mpr (hlim (step X a))).tendsto_at (Set.mem_univ x))

end Langlands.Geometry.Manifold
