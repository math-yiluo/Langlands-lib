import Langlands.Geometry.Manifold.SmoothGroupUniformLimit

/-! # Passing a single invariant differential through a locally uniform limit -/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
  {ι : Type*} {l : Filter ι} [l.NeBot]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "J" => Fin (Module.finrank ℝ E)

/-- The locally uniform limits of the first invariant derivatives are the
actual first invariant derivatives of the smooth limit. -/
theorem groupDirectionalValue_of_tendstoLocallyUniformly
    {f : ι → G → ℂ} {g : G → ℂ} {D : GroupLieAlgebra 𝓘E G → G → ℂ}
    (hf : ∀ i, ContMDiff 𝓘E 𝓘ℂ ∞ (f i)) (hg : ContMDiff 𝓘E 𝓘ℂ ∞ g)
    (hlim : TendstoLocallyUniformly f g l)
    (hD : ∀ X, TendstoLocallyUniformly (fun i => groupDirectionalValue 𝓘E X (f i)) (D X) l)
    (X : GroupLieAlgebra 𝓘E G) (x : G) :
    groupDirectionalValue 𝓘E X g x = D X x := by
  let e := extChartAt 𝓘E (1 : G)
  let ψ (y : E) := x * e.symm y
  have hS : IsOpen e.target := isOpen_extChartAt_target (I := 𝓘E) (1 : G)
  have he : e 1 ∈ e.target := e.map_source (mem_extChartAt_source (1 : G))
  have he₁ : e.symm (e 1) = 1 := e.left_inv (mem_extChartAt_source (1 : G))
  have hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ e.target :=
    contMDiffOn_const.mul (contMDiffOn_extChartAt_symm (1 : G))
  obtain ⟨Y, L, hL, hformula⟩ := exists_invariantDerivativeExpansion ψ hS hψ
  let B (i : ι) (y : E) : E →L[ℝ] ℂ :=
    invariantCoordinateDerivative (fun j => L j y)
      (fun j => groupDirectionalValue 𝓘E (Y j) (f i) (ψ y))
  let C (y : E) : E →L[ℝ] ℂ :=
    invariantCoordinateDerivative (fun j => L j y) (fun j => D (Y j) (ψ y))
  have hB (i : ι) (y : E) (hy : y ∈ e.target) : HasFDerivAt (f i ∘ ψ) (B i y) y :=
    hformula (f i) (hf i) y hy
  have hBC : TendstoLocallyUniformlyOn B C l e.target := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro y hy
    rw [tendstoUniformlyOnFilter_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
      tendsto_comap_iff]
    let t := l ×ˢ 𝓝[e.target] y
    have htest (j : J) : Tendsto (fun p : ι × E =>
        -D (Y j) (ψ p.2) + groupDirectionalValue 𝓘E (Y j) (f p.1) (ψ p.2)) t (𝓝 0) := by
      have hj := (tendstoLocallyUniformlyOn_univ.mpr (hD (Y j))).comp ψ
        (mapsTo_univ _ _) hψ.continuousOn
      have ht := tendstoLocallyUniformlyOn_iff_filter.mp hj y hy
      rwa [tendstoUniformlyOnFilter_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
        tendsto_comap_iff] at ht
    have hcoef (j : J) : Tendsto (fun p : ι × E => L j p.2) t (𝓝 (L j y)) :=
      (show Tendsto (L j) (𝓝[e.target] y) (𝓝 (L j y)) from
        (hL j).continuousOn y hy).comp tendsto_snd
    have hsmul (c : E →L[ℝ] ℝ) (v : ℂ) :
        ContinuousLinearMap.smulRightL ℝ E ℂ c v = c.smulRight v := rfl
    have hsum : Tendsto (fun p : ι × E => ∑ j, (L j p.2).smulRight
        (-D (Y j) (ψ p.2) + groupDirectionalValue 𝓘E (Y j) (f p.1) (ψ p.2))) t (𝓝 0) := by
      have hj (j : J) :=
        ((ContinuousLinearMap.smulRightL ℝ E ℂ).isBoundedBilinearMap.continuous.tendsto
          (L j y, 0)).comp ((hcoef j).prodMk_nhds (htest j))
      simpa only [Function.comp_def, hsmul, ContinuousLinearMap.smulRight_zero,
        Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hj j)
    simpa only [Function.comp_def, B, C, invariantCoordinateDerivative, ← hsmul,
      map_add, map_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib] using hsum
  have hc := (tendstoLocallyUniformlyOn_univ.mpr hlim).comp ψ
    (mapsTo_univ _ _) hψ.continuousOn
  have hC : HasFDerivAt (g ∘ ψ) (C (e 1)) (e 1) :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hS hBC hB
      (fun y hy => hc.tendsto_at hy) he
  have htrans (u : G → ℂ) (hu : ContMDiff 𝓘E 𝓘ℂ ∞ u) :
      fderiv ℝ (u ∘ ψ) (e 1) X = groupDirectionalValue 𝓘E X u x := by
    let v (y : G) := u (x * y)
    have hv : ContMDiff 𝓘E 𝓘ℂ ∞ v := hu.comp (contMDiff_const.mul contMDiff_id)
    have hMD : MDifferentiableAt 𝓘E 𝓘E (e.symm : E → G) (e 1) :=
      ((contMDiffOn_extChartAt_symm (I := 𝓘E) (n := ∞) (1 : G) (e 1) he).contMDiffAt
        (hS.mem_nhds he)).mdifferentiableAt (by simp)
    change fderiv ℝ (v ∘ e.symm) (e 1) X = mvfderiv 𝓘E v 1 X
    have hcomp := mvfderiv_comp_apply_of_eq (I := 𝓘E) (I' := 𝓘E) (e 1)
      (hv.mdifferentiableAt (by simp)) hMD he₁ (X : TangentSpace 𝓘E (e 1))
    have hid := mfderivWithin_range_extChartAt_symm (I := 𝓘E) (x := (1 : G))
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
    have hid' : mfderiv 𝓘E 𝓘E (e.symm : E → G) (e 1) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘E (e 1)) := hid
    rw [hid'] at hcomp
    change mvfderiv 𝓘E (v ∘ e.symm) (e 1) X = mvfderiv 𝓘E v 1 X at hcomp
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] at hcomp
    exact hcomp
  have hBi (i : ι) : B i (e 1) X = groupDirectionalValue 𝓘E X (f i) x :=
    (congrArg (fun d : E →L[ℝ] ℂ => d X) (hB i (e 1) he).fderiv.symm).trans (htrans _ (hf i))
  have hCi : C (e 1) X = groupDirectionalValue 𝓘E X g x :=
    (congrArg (fun d : E →L[ℝ] ℂ => d X) hC.fderiv.symm).trans (htrans _ hg)
  have ht := ((ContinuousLinearMap.apply (E' := E) ℝ ℂ X).continuous.tendsto _).comp
    (hBC.tendsto_at he)
  change Tendsto (fun i => B i (e 1) X) l (𝓝 (C (e 1) X)) at ht
  rw [funext hBi, hCi] at ht
  exact tendsto_nhds_unique ht ((tendstoLocallyUniformlyOn_univ.mpr (hD X)).tendsto_at (mem_univ x))

end Langlands.Geometry.Manifold
