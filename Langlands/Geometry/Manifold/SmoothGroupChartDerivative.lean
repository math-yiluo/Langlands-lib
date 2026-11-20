import Langlands.Geometry.Manifold.SmoothGroupDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Coordinate derivatives in an invariant frame -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "J" => Fin (Module.finrank ℝ E)

omit [FiniteDimensional ℝ E] [LieGroup 𝓘E ∞ G] in
/-- The inverse of the identity chart sends a model tangent direction to the
corresponding Lie algebra direction. -/
def identityChartLieDirection (v : E) : GroupLieAlgebra 𝓘E G :=
  let e := extChartAt 𝓘E (1 : G)
  mfderiv 𝓘E 𝓘E (e.symm : E → G) (e 1) v

/-- In a smooth parametrization by a finite-dimensional coordinate space, the
coordinate derivative of a smooth complex function is a finite combination of
its invariant derivatives, with smooth coefficient linear forms. -/
theorem exists_invariantDerivativeExpansion (ψ : E → G) {S : Set E} (hS : IsOpen S)
    (hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ S) :
    ∃ (X : J → GroupLieAlgebra 𝓘E G) (L : J → E → E →L[ℝ] ℝ),
      (∀ j, ContDiffOn ℝ ∞ (L j) S) ∧ ∀ (f : G → ℂ),
      ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f → ∀ x ∈ S,
      HasFDerivAt (f ∘ ψ)
        (∑ j, (L j x).smulRight (groupDirectionalValue 𝓘E (X j) f (ψ x))) x := by
  classical
  let e := extChartAt 𝓘E (1 : G)
  have he₁ : (1 : G) ∈ e.source := mem_extChartAt_source _
  have heInv : e.symm (e 1) = 1 := e.left_inv he₁
  have heSmooth : ContMDiffAt 𝓘E 𝓘E ∞ (e.symm : E → G) (e 1) := by
    refine (contMDiffOn_extChartAt_symm (I := 𝓘E) (n := ∞) (1 : G)
      (e 1) (e.map_source he₁)).contMDiffAt ?_
    exact (isOpen_extChartAt_target (I := 𝓘E) (1 : G)).mem_nhds (e.map_source he₁)
  let b := Module.finBasis ℝ E
  let c (j : J) : E →L[ℝ] ℝ := (b.coord j).toContinuousLinearMap
  let X (j : J) : GroupLieAlgebra 𝓘E G := identityChartLieDirection (b j)
  let H (p : E × E) : E := e ((ψ p.1)⁻¹ * ψ p.2)
  let B : Set (E × E) := (S ×ˢ S) ∩ (fun p => (ψ p.1)⁻¹ * ψ p.2) ⁻¹' e.source
  have hdivision : ContMDiffOn 𝓘(ℝ, E × E) 𝓘E ∞
      (fun p : E × E => (ψ p.1)⁻¹ * ψ p.2) (S ×ˢ S) := by
    intro p hp
    have h₁ : ContMDiffAt 𝓘(ℝ, E × E) 𝓘E ∞ (fun p : E × E => ψ p.1) p :=
      ((hψ p.1 hp.1).contMDiffAt (hS.mem_nhds hp.1)).comp p
        (contDiff_fst.contMDiff.contMDiffAt)
    have h₂ : ContMDiffAt 𝓘(ℝ, E × E) 𝓘E ∞ (fun p : E × E => ψ p.2) p :=
      ((hψ p.2 hp.2).contMDiffAt (hS.mem_nhds hp.2)).comp p
        (contDiff_snd.contMDiff.contMDiffAt)
    exact (h₁.inv.mul h₂).contMDiffWithinAt
  have hB : IsOpen B := hdivision.continuousOn.isOpen_inter_preimage (hS.prod hS)
    (isOpen_extChartAt_source (I := 𝓘E) (1 : G))
  have hBdiag (x : E) (hx : x ∈ S) : (x, x) ∈ B :=
    ⟨⟨hx, hx⟩, by simpa using he₁⟩
  have hH : ContDiffOn ℝ ∞ H B := by
    rw [← contMDiffOn_iff_contDiffOn]
    intro p hp
    have hp₀ : (ψ p.1)⁻¹ * ψ p.2 ∈ (chartAt E (1 : G)).source := by
      rw [← extChartAt_source (I := 𝓘E)]
      exact hp.2
    exact ((contMDiffAt_extChartAt' (I := 𝓘E) (n := ∞) hp₀).comp p
      ((hdivision p hp.1).contMDiffAt ((hS.prod hS).mem_nhds hp.1))).contMDiffWithinAt
  let D (x : E) : E →L[ℝ] E :=
    (fderiv ℝ H (x, x)).comp (ContinuousLinearMap.inr ℝ E E)
  have hD : ContDiffOn ℝ ∞ D S := by
    have hd : ContDiffOn ℝ ∞ (fun x : E => fderiv ℝ H (x, x)) S :=
      (hH.fderiv_of_isOpen hB (by simp)).comp (contDiff_id.prodMk contDiff_id).contDiffOn
        hBdiag
    exact (((ContinuousLinearMap.compL ℝ E (E × E) E).flip
      (ContinuousLinearMap.inr ℝ E E)).contDiff.comp_contDiffOn hd)
  let L (j : J) (x : E) := (c j).comp (D x)
  refine ⟨X, L, fun j => ?_, fun f hf x hx => ?_⟩
  · exact ((ContinuousLinearMap.compL ℝ E E ℝ (c j)).contDiff.comp_contDiffOn hD)
  · let q := ψ x
    let a (t : E) := f (q * e.symm t)
    let s (t : E) := H (x, t)
    have hsx : s x = e 1 := by simp [s, H]
    have haSmooth : ContDiffAt ℝ ∞ a (e 1) :=
      (hf.contMDiffAt.comp (e 1) (contMDiffAt_const.mul heSmooth)).contDiffAt
    have hs : HasFDerivAt s (D x) x := by
      have hProd : HasFDerivAt (fun t : E => (x, t))
          (ContinuousLinearMap.inr ℝ E E) x := by
        convert (hasFDerivAt_const x x).prodMk (hasFDerivAt_id x) using 1 <;> rfl
      have hDiff := (hH (x, x) (hBdiag x hx)).contDiffAt (hB.mem_nhds (hBdiag x hx))
      exact (hDiff.differentiableAt (by simp)).hasFDerivAt.comp x hProd
    have hEq : a ∘ s =ᶠ[𝓝 x] f ∘ ψ := by
      have hmem : ∀ᶠ t in 𝓝 x, (x, t) ∈ B :=
        (continuous_const.prodMk continuous_id).continuousAt (x := x)
          (hB.mem_nhds (hBdiag x hx))
      filter_upwards [hmem] with t ht
      change f (q * e.symm (e ((ψ x)⁻¹ * ψ t))) = f (ψ t)
      rw [e.left_inv ht.2]
      simp [q]
    have hd₀ : HasFDerivAt (f ∘ ψ) ((fderiv ℝ a (e 1)).comp (D x)) x := by
      have ha : HasFDerivAt a (fderiv ℝ a (e 1)) (s x) := by
        rw [hsx]
        exact (haSmooth.differentiableAt (by simp)).hasFDerivAt
      exact (ha.comp x hs).congr_of_eventuallyEq hEq.symm
    have hb (j : J) : fderiv ℝ a (e 1) (b j) =
        groupDirectionalValue 𝓘E (X j) f (ψ x) := by
      let f₀ (y : G) := f (q * y)
      have h₀ : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f₀ :=
        hf.comp (contMDiff_const.mul contMDiff_id)
      change fderiv ℝ (f₀ ∘ e.symm) (e 1) (b j) =
        mvfderiv 𝓘E f₀ 1 (mfderiv 𝓘E 𝓘E (e.symm : E → G) (e 1) (b j))
      rw [← mvfderiv_eq_fderiv]
      exact mvfderiv_comp_apply_of_eq (I := 𝓘E) (I' := 𝓘E) (e 1)
        (h₀.mdifferentiableAt (by simp)) (heSmooth.mdifferentiableAt (by simp)) heInv (b j)
    convert hd₀ using 1
    ext y
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      L, ← hb, ← map_smul, ← map_sum]
    exact congrArg (fderiv ℝ a (e 1)) (b.sum_repr (D x y))

end Langlands.Geometry.Manifold
