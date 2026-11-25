import Langlands.Geometry.Manifold.LieGroupEllipticEstimateStatement
import Langlands.Analysis.VectorFieldWordCoefficients
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-! # Left-invariant word derivatives in a Euclidean chart at the identity -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

open Langlands.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] [ChartedSpace E H] [Group H] [LieGroup 𝓘(ℝ, E) ∞ H]
  {n : ℕ}

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "F" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [Group H] [LieGroup 𝓘(ℝ, E) ∞ H] in
/-- Locally equal complex functions have the same derivative at the point. -/
private theorem mvfderiv_apply_congr {g₁ g : H → ℂ} {y : H} (hL : g₁ =ᶠ[𝓝 y] g)
    (v : TangentSpace 𝓘E y) : mvfderiv 𝓘E g₁ y v = mvfderiv 𝓘E g y v := by
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, hL.mfderiv_eq]
  rfl

/-- **Euclidean chart frame at the identity.** There are an open set `S` of the Euclidean
space of dimension `finrank ℝ E`, a smooth parametrization `ψ : S → H` hitting `1` at a point
`x₀ ∈ S`, and smooth vector fields `V i` on `S` with `V i x₀ = toEuclidean (X i)`, such that
the derivative along `X i` of a smooth function `f` at `ψ x` is the directional derivative of
`f ∘ ψ` at `x` along `V i x`. -/
theorem exists_lieGroupChartFrame (X : Fin n → GroupLieAlgebra 𝓘E H) :
    ∃ (S : Set F) (ψ : F → H) (x₀ : F) (V : Fin n → F → F),
      IsOpen S ∧ x₀ ∈ S ∧ ψ x₀ = 1 ∧ ContMDiffOn 𝓘(ℝ, F) 𝓘E ∞ ψ S ∧
      (∀ i, ContDiffOn ℝ ∞ (V i) S) ∧ (∀ i, V i x₀ = toEuclidean (X i : E)) ∧
      ∀ f : H → ℂ, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f → ∀ i, ∀ x ∈ S,
        groupDirectionalValue 𝓘E (X i) f (ψ x) = fderiv ℝ (f ∘ ψ) x (V i x) := by
  classical
  let L : E ≃L[ℝ] F := toEuclidean
  let e := extChartAt 𝓘E (1 : H)
  have he₁ : (1 : H) ∈ e.source := mem_extChartAt_source _
  have hTo : IsOpen e.target := isOpen_extChartAt_target (1 : H)
  have hSo : IsOpen e.source := isOpen_extChartAt_source (1 : H)
  let S : Set F := L.symm ⁻¹' e.target
  have hS : IsOpen S := hTo.preimage L.symm.continuous
  let ψ : F → H := fun x => e.symm (L.symm x)
  have hψS (x : F) (hx : x ∈ S) : ψ x ∈ e.source := e.map_target hx
  have hLψ (x : F) (hx : x ∈ S) : L (e (ψ x)) = x := by
    change L (e (e.symm (L.symm x))) = x
    rw [e.right_inv hx]
    exact L.apply_symm_apply x
  have hesymm : ContMDiffOn 𝓘E 𝓘E ∞ e.symm e.target := contMDiffOn_extChartAt_symm (1 : H)
  have hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘E ∞ ψ S :=
    hesymm.comp (L.symm.contDiff (n := ∞)).contMDiff.contMDiffOn (fun x hx => hx)
  -- the joint map `(x, z) ↦ ψ x * e⁻¹ z` and its chart image
  let P : F × E → H := fun p => ψ p.1 * e.symm p.2
  have hP : ContMDiffOn 𝓘(ℝ, F × E) 𝓘E ∞ P (S ×ˢ e.target) := by
    intro p hp
    have h₁ : ContMDiffAt 𝓘(ℝ, F × E) 𝓘E ∞ (fun p : F × E => ψ p.1) p :=
      ((hψ p.1 hp.1).contMDiffAt (hS.mem_nhds hp.1)).comp p
        (contDiff_fst.contMDiff.contMDiffAt)
    have h₂ : ContMDiffAt 𝓘(ℝ, F × E) 𝓘E ∞ (fun p : F × E => e.symm p.2) p :=
      ((hesymm p.2 hp.2).contMDiffAt (hTo.mem_nhds hp.2)).comp p
        (contDiff_snd.contMDiff.contMDiffAt)
    exact (h₁.mul h₂).contMDiffWithinAt
  let B : Set (F × E) := (S ×ˢ e.target) ∩ P ⁻¹' e.source
  have hB : IsOpen B := hP.continuousOn.isOpen_inter_preimage (hS.prod hTo) hSo
  let m : F × E → F := fun p => L (e (P p))
  have hm : ContDiffOn ℝ ∞ m B := by
    have h : ContDiffOn ℝ ∞ (fun p => e (P p)) B := by
      rw [← contMDiffOn_iff_contDiffOn]
      intro p hp
      have hp₀ : P p ∈ (chartAt E (1 : H)).source := by
        rw [← extChartAt_source (I := 𝓘E)]
        exact hp.2
      exact ((contMDiffAt_extChartAt' (I := 𝓘E) (n := ∞) hp₀).comp p
        ((hP p hp.1).contMDiffAt ((hS.prod hTo).mem_nhds hp.1))).contMDiffWithinAt
    exact L.contDiff.comp_contDiffOn h
  have hBx (x : F) (hx : x ∈ S) : (x, e 1) ∈ B := by
    refine ⟨⟨hx, e.map_source he₁⟩, ?_⟩
    change ψ x * e.symm (e 1) ∈ e.source
    rw [e.left_inv he₁, mul_one]
    exact hψS x hx
  have hmx (x : F) (hx : x ∈ S) : m (x, e 1) = x := by
    change L (e (ψ x * e.symm (e 1))) = x
    rw [e.left_inv he₁, mul_one]
    exact hLψ x hx
  have hpart (x : F) (hx : x ∈ S) : HasFDerivAt (fun z : E => m (x, z))
      ((fderiv ℝ m (x, e 1)).comp (ContinuousLinearMap.inr ℝ F E)) (e 1) := by
    have hDiff : DifferentiableAt ℝ m (x, e 1) :=
      ((hm (x, e 1) (hBx x hx)).contDiffAt (hB.mem_nhds (hBx x hx))).differentiableAt
        (by simp)
    exact hDiff.hasFDerivAt.comp (e 1) (hasFDerivAt_prodMk_right x (e 1))
  let V (i : Fin n) (x : F) : F :=
    fderiv ℝ m (x, e 1) (ContinuousLinearMap.inr ℝ F E (X i : E))
  -- the base point
  let x₀ : F := L (e 1)
  have hx₀ : x₀ ∈ S := by
    change L.symm (L (e 1)) ∈ e.target
    rw [L.symm_apply_apply]
    exact e.map_source he₁
  have hψ₀ : ψ x₀ = 1 := by
    change e.symm (L.symm (L (e 1))) = 1
    rw [L.symm_apply_apply, e.left_inv he₁]
  refine ⟨S, ψ, x₀, V, hS, hx₀, hψ₀, hψ, fun i => ?_, fun i => ?_, fun f hf i x hx => ?_⟩
  · -- smoothness of the vector fields
    have hd : ContDiffOn ℝ ∞ (fun x : F => fderiv ℝ m (x, e 1)) S :=
      (hm.fderiv_of_isOpen hB (by simp)).comp
        (contDiff_id.prodMk (contDiff_const (c := e 1))).contDiffOn hBx
    exact hd.clm_apply contDiffOn_const
  · -- value at the base point: near `e 1`, `z ↦ m (x₀, z)` is `L`
    have hEq : (fun z : E => m (x₀, z)) =ᶠ[𝓝 (e 1)] L := by
      filter_upwards [hTo.mem_nhds (e.map_source he₁)] with z hz
      change L (e (ψ x₀ * e.symm z)) = L z
      rw [hψ₀, one_mul, e.right_inv hz]
    have hL : HasFDerivAt (fun z : E => m (x₀, z)) (L : E →L[ℝ] F) (e 1) :=
      L.hasFDerivAt.congr_of_eventuallyEq hEq
    have h := (hpart x₀ hx₀).unique hL
    exact congrArg (fun T : E →L[ℝ] F => T (X i : E)) h
  · -- the chain rule through the chart
    have hfψ : ContDiffOn ℝ ∞ (f ∘ ψ) S :=
      contMDiffOn_iff_contDiffOn.1 (hf.comp_contMDiffOn hψ)
    have hfψx : DifferentiableAt ℝ (f ∘ ψ) x :=
      ((hfψ x hx).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
    let a : E → ℂ := fun z => (f ∘ ψ) (m (x, z))
    have ha : HasFDerivAt a ((fderiv ℝ (f ∘ ψ) x).comp
        ((fderiv ℝ m (x, e 1)).comp (ContinuousLinearMap.inr ℝ F E))) (e 1) := by
      have h1 : HasFDerivAt (f ∘ ψ) (fderiv ℝ (f ∘ ψ) x) (m (x, e 1)) := by
        rw [hmx x hx]
        exact hfψx.hasFDerivAt
      exact h1.comp (e 1) (hpart x hx)
    have hloc : (fun h : H => f (ψ x * h)) =ᶠ[𝓝 (1 : H)] a ∘ e := by
      have hmul : ContinuousAt (fun h : H => ψ x * h) 1 :=
        ((contMDiff_const.mul contMDiff_id : ContMDiff 𝓘E 𝓘E ∞ (fun h : H => ψ x * h))
          ).continuous.continuousAt
      have h1 : ∀ᶠ h in 𝓝 (1 : H), ψ x * h ∈ e.source :=
        hmul (by simpa using hSo.mem_nhds (hψS x hx))
      filter_upwards [hSo.mem_nhds he₁, h1] with h hh hxh
      change f (ψ x * h) = f (e.symm (L.symm (L (e (ψ x * e.symm (e h))))))
      rw [e.left_inv hh, L.symm_apply_apply, e.left_inv hxh]
    have he : MDifferentiableAt 𝓘E 𝓘E e 1 := mdifferentiableAt_extChartAt (mem_chart_source E 1)
    have haM : MDifferentiableAt 𝓘E 𝓘(ℝ, ℂ) a (e 1) :=
      ha.differentiableAt.mdifferentiableAt
    change mvfderiv 𝓘E (fun h => f (ψ x * h)) 1 (X i) = _
    rw [mvfderiv_apply_congr hloc,
      mvfderiv_comp_apply_of_eq (I := 𝓘E) (I' := 𝓘E) (1 : H) haM he rfl,
      mfderiv_extChartAt_self, mvfderiv_eq_fderiv, ha.fderiv]
    rfl

omit [FiniteDimensional ℝ E] [LieGroup 𝓘(ℝ, E) ∞ H] in
/-- The word `i :: w` acts by differentiating along `X i` after the word `w`. -/
theorem lieWordDerivative_ofList_cons (X : Fin n → GroupLieAlgebra 𝓘E H) (i : Fin n)
    (w : List (Fin n)) (φ : H → ℂ) :
    (lieWordDerivative X (FreeMonoid.ofList (i :: w)) : (H → ℂ) → H → ℂ) φ =
      groupDirectionalValue 𝓘E (X i)
        ((lieWordDerivative X (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ) := by
  rw [show FreeMonoid.ofList (i :: w) = FreeMonoid.of i * FreeMonoid.ofList w from rfl, map_mul]
  rfl

omit [FiniteDimensional ℝ E] [LieGroup 𝓘(ℝ, E) ∞ H] in
/-- The empty word acts as the identity. -/
theorem lieWordDerivative_ofList_nil (X : Fin n → GroupLieAlgebra 𝓘E H) (φ : H → ℂ) :
    (lieWordDerivative X (FreeMonoid.ofList []) : (H → ℂ) → H → ℂ) φ = φ := by
  rw [show FreeMonoid.ofList ([] : List (Fin n)) = 1 from rfl, map_one]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Word derivatives of smooth functions are smooth. -/
theorem contMDiff_lieWordDerivative_ofList (X : Fin n → GroupLieAlgebra 𝓘E H) {φ : H → ℂ}
    (hφ : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ φ) :
    ∀ w : List (Fin n),
      ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ ((lieWordDerivative X (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ)
  | [] => by rw [lieWordDerivative_ofList_nil]; exact hφ
  | i :: w => by
      rw [lieWordDerivative_ofList_cons]
      exact contMDiff_groupDirectionalValue 𝓘E (X i) (contMDiff_lieWordDerivative_ofList X hφ w)

/-- **Coordinate expansion of word derivatives.** In a chart frame as in
`exists_lieGroupChartFrame`, the derivative of a smooth function `φ` along a word of length at
most `N`, evaluated at `ψ x`, is the combination of the ordered coordinate derivatives of
`φ ∘ ψ` at `x` of order at most `N` with the coefficients `vectorFieldWordCoeff V w`. -/
theorem lieWordDerivative_chart_expansion (X : Fin n → GroupLieAlgebra 𝓘E H) {S : Set F}
    (hS : IsOpen S) {ψ : F → H} (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘E ∞ ψ S) {V : Fin n → F → F}
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) S)
    (hdir : ∀ f : H → ℂ, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f → ∀ i, ∀ x ∈ S,
      groupDirectionalValue 𝓘E (X i) f (ψ x) = fderiv ℝ (f ∘ ψ) x (V i x))
    {φ : H → ℂ} (hφ : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ φ) (w : List (Fin n)) (N : ℕ)
    (hN : w.length ≤ N) (x : F) (hx : x ∈ S) :
    (lieWordDerivative X (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ (ψ x) =
      ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin (Module.finrank ℝ E),
        vectorFieldWordCoeff V w k W x *
          iteratedFDeriv ℝ k (φ ∘ ψ) x
            (fun q => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (W q)) := by
  have hu : ContDiffOn ℝ ∞ (φ ∘ ψ) S := contMDiffOn_iff_contDiffOn.1 (hφ.comp_contMDiffOn hψ)
  refine vectorFieldWord_expansion hS hV hu
    (fun w y => (lieWordDerivative X (FreeMonoid.ofList w) : (H → ℂ) → H → ℂ) φ (ψ y))
    (fun y _ => by rw [lieWordDerivative_ofList_nil]; rfl) (fun i w y hy => ?_) w N hN x hx
  rw [lieWordDerivative_ofList_cons]
  exact hdir _ (contMDiff_lieWordDerivative_ofList X hφ w) i y hy

end Langlands.Geometry.Manifold
