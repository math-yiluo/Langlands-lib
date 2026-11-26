import Langlands.Geometry.Manifold.LieGroupEllipticChart
import Langlands.Analysis.LocalEllipticInteriorBounds

/-! # Proof of the interior estimate for elliptic left-invariant word operators -/

noncomputable section

universe u v

open Set Filter Metric
open scoped Manifold ContDiff Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

open Langlands.Analysis

/-- The top-order pairing of `vectorFieldWordCoeff_symbol`, for a word of a prescribed length. -/
private theorem vectorFieldWordCoeff_symbol_of_length {d n : ℕ}
    (V : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (ξ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (w : List (Fin n))
    (k : ℕ) (hw : w.length = k) :
    ∑ W : Fin k → Fin d, vectorFieldWordCoeff V w k W x *
      ∏ j : Fin k, ((ξ (EuclideanSpace.basisFun (Fin d) ℝ (W j)) : ℝ) : ℂ) =
        (w.map fun a => ((ξ (V a x) : ℝ) : ℂ)).prod := by
  subst hw
  exact vectorFieldWordCoeff_symbol V x ξ w

/-- A word combination acts pointwise by the finite sum over its support. -/
private theorem lieWordAction_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] [ChartedSpace E H] [Group H] [LieGroup 𝓘(ℝ, E) ∞ H] {n : ℕ}
    (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H) (P : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (φ : H → ℂ) (y : H) :
    lieWordAction X P φ y = ∑ w ∈ P.coeff.support,
      P.coeff w * (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ y := by
  simp only [lieWordAction, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- In the Euclidean identity chart, an elliptic word operator is a scalar coordinate operator
with smooth coefficients and the specified principal symbol at the identity. The same frame
also expands any word used to test derivatives of solutions. -/
theorem exists_lieWordCoordinateOperator {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type v} [TopologicalSpace H] [ChartedSpace E H] [Group H]
    [LieGroup 𝓘(ℝ, E) ∞ H] {n r : ℕ} (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (hPtop : ∀ w ∈ Ptop.coeff.support, w.length = r)
    (hPlow : ∀ w ∈ Plow.coeff.support, w.length < r)
    (hell : ∀ ξ : GroupLieAlgebra 𝓘(ℝ, E) H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0) :
    let d := Module.finrank ℝ E
    let F := EuclideanSpace ℝ (Fin d)
    let L : E ≃L[ℝ] F := toEuclidean
    let e := extChartAt 𝓘(ℝ, E) (1 : H)
    let S := L.symm ⁻¹' e.target
    let ψ := e.symm ∘ L.symm
    let x₀ := L (e 1)
    ∃ (D : CoordinateScalarOperator F d r) (V : Fin n → F → F),
      IsOpen S ∧ x₀ ∈ S ∧ ψ x₀ = 1 ∧ ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ S ∧
      D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis ∧
      (∀ (k : Fin (r + 1)) (W : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k W) S) ∧
      (∀ ξ : F →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0) ∧
      (∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ → ∀ x ∈ S,
        D.action (φ ∘ ψ) x = lieWordAction X (Ptop + Plow) φ (ψ x)) ∧
      ∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ →
        ∀ (w : FreeMonoid (Fin n)) (N : ℕ), w.length ≤ N → ∀ x ∈ S,
          (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ (ψ x) =
            ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
              vectorFieldWordCoeff V w.toList k W x *
                iteratedFDeriv ℝ k (φ ∘ ψ) x
                  (fun q => EuclideanSpace.basisFun (Fin d) ℝ (W q)) := by
  classical
  let d := Module.finrank ℝ E
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  obtain ⟨S, ψ, x₀, V, hS, hx₀, hψ₀, hψ, rfl, rfl, rfl, hV, hVx₀, hdir⟩ :=
    exists_lieGroupChartFrame_extChart X
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) := toEuclidean
  let chart := extChartAt 𝓘(ℝ, E) (1 : H)
  let S := L.symm ⁻¹' chart.target
  let ψ := chart.symm ∘ L.symm
  let x₀ := L (chart 1)
  -- the operator in the chart
  let P := Ptop + Plow
  have hlen : ∀ w ∈ P.coeff.support, w.length ≤ r := by
    intro w hw
    have hw' : w ∈ (Ptop.coeff + Plow.coeff).support := hw
    rcases Finset.mem_union.1 (Finsupp.support_add hw') with h | h
    · exact (hPtop w h).le
    · exact (hPlow w h).le
  let D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r :=
    { basis := e.toBasis
      coefficient := fun k W x => ∑ w ∈ P.coeff.support,
        P.coeff w * vectorFieldWordCoeff V (FreeMonoid.toList w) k.val W x }
  have hcoef : ∀ (k : Fin (r + 1)) (W : Fin k.val → Fin d),
      ContDiffOn ℝ ∞ (D.coefficient k W) S := fun k W =>
    ContDiffOn.sum fun w _ => contDiffOn_const.mul (contDiffOn_vectorFieldWordCoeff hS hV _ _ _)
  have hexp : ∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ →
      ∀ (w : FreeMonoid (Fin n)) (N : ℕ), w.length ≤ N → ∀ x ∈ S,
        (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ (ψ x) =
          ∑ k ∈ Finset.range (N + 1), ∑ W : Fin k → Fin d,
            vectorFieldWordCoeff V w.toList k W x *
              iteratedFDeriv ℝ k (φ ∘ ψ) x (fun q => e (W q)) :=
    fun φ hφ w N hN x hx => lieWordDerivative_chart_expansion X hS hψ hV hdir hφ w.toList N hN x hx
  have haction : ∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ → ∀ x ∈ S,
      D.action (φ ∘ ψ) x = lieWordAction X P φ (ψ x) := by
    intro φ hφ x hx
    have hR : lieWordAction X P φ (ψ x) = ∑ w ∈ P.coeff.support, ∑ k : Fin (r + 1),
        ∑ W : Fin k.val → Fin d, P.coeff w * vectorFieldWordCoeff V w.toList k.val W x *
          iteratedFDeriv ℝ k.val (φ ∘ ψ) x (fun j => e (W j)) := by
      rw [lieWordAction_apply]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hexp φ hφ w r (hlen w hw) x hx, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun W _ => ?_
      ring
    rw [hR, Finset.sum_comm (s := P.coeff.support)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm (s := P.coeff.support)]
    refine Finset.sum_congr rfl fun W _ => ?_
    simp only [D, Finset.sum_mul, OrthonormalBasis.coe_toBasis]
  -- the principal symbol at the chart point
  have hsymb (ξ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
      D.principalSymbol x₀ ξ = lieWordSymbol X
        ((ξ.comp (toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap
          ).toLinearMap) Ptop := by
    let ξ' : GroupLieAlgebra 𝓘(ℝ, E) H →ₗ[ℝ] ℝ :=
      (ξ.comp (toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap).toLinearMap
    let T : FreeMonoid (Fin n) → ℂ := fun w => ∑ W : Fin r → Fin d,
      vectorFieldWordCoeff V w.toList r W x₀ * ∏ j : Fin r, ((ξ (e (W j)) : ℝ) : ℂ)
    let g : FreeMonoid (Fin n) → ℂ := fun w =>
      (w.toList.map fun a => ((ξ' (X a) : ℝ) : ℂ)).prod
    have h1 : D.principalSymbol x₀ ξ = ∑ w ∈ P.coeff.support, P.coeff w * T w := by
      simp only [CoordinateScalarOperator.principalSymbol, D, T, OrthonormalBasis.coe_toBasis,
        Fin.val_last, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    have h2 : lieWordSymbol X ξ' Ptop = ∑ w ∈ Ptop.coeff.support, Ptop.coeff w * g w := by
      rw [lieWordSymbol, MonoidAlgebra.lift_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [FreeMonoid.lift_apply, smul_eq_mul]
    have hclaim : ∀ w ∈ P.coeff.support ∪ Ptop.coeff.support,
        P.coeff w * T w = Ptop.coeff w * g w := by
      intro w hw
      have hle : w.length ≤ r := by
        rcases Finset.mem_union.1 hw with h | h
        · exact hlen w h
        · exact (hPtop w h).le
      rcases hle.lt_or_eq with hlt | heq
      · have hT : T w = 0 := Finset.sum_eq_zero fun W _ => by
          rw [vectorFieldWordCoeff_eq_zero V w.toList r W hlt]
          simp
        have hP : Ptop.coeff w = 0 := by
          by_contra h
          exact hlt.ne (hPtop w (Finsupp.mem_support_iff.2 h))
        rw [hT, hP]
        simp
      · have hL : Plow.coeff w = 0 := by
          by_contra h
          exact (hPlow w (Finsupp.mem_support_iff.2 h)).ne heq
        have hT : T w = g w := by
          change ∑ W : Fin r → Fin d, vectorFieldWordCoeff V w.toList r W x₀ *
            ∏ j : Fin r, ((ξ (e (W j)) : ℝ) : ℂ) = _
          rw [vectorFieldWordCoeff_symbol_of_length V x₀ ξ w.toList r heq]
          refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
          rw [hVx₀ a]
          rfl
        have hPc : P.coeff w = Ptop.coeff w := by
          simp only [P, MonoidAlgebra.coeff_add, Finsupp.add_apply, hL, add_zero]
        rw [hPc, hT]
    change D.principalSymbol x₀ ξ = lieWordSymbol X ξ' Ptop
    rw [h1, h2]
    calc ∑ w ∈ P.coeff.support, P.coeff w * T w
        = ∑ w ∈ P.coeff.support ∪ Ptop.coeff.support, P.coeff w * T w := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.1 hw, zero_mul]
      _ = ∑ w ∈ P.coeff.support ∪ Ptop.coeff.support, Ptop.coeff w * g w :=
          Finset.sum_congr rfl hclaim
      _ = ∑ w ∈ Ptop.coeff.support, Ptop.coeff w * g w := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [Finsupp.notMem_support_iff.1 hw, zero_mul]
  have hellD : ∀ ξ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x₀ ξ ≠ 0 := by
    intro ξ hξ
    rw [hsymb]
    refine hell _ fun h => hξ (ContinuousLinearMap.ext fun v => ?_)
    have hv := LinearMap.congr_fun h
      ((toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)).symm v)
    rw [zero_apply,
      ← ContinuousLinearEquiv.apply_symm_apply (toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)) v]
    exact hv
  exact ⟨D, V, hS, hx₀, hψ₀, hψ, rfl, hcoef, hellD, haction, hexp⟩

/-- **Interior estimate for elliptic left-invariant word operators on a Lie group.** In a
Euclidean chart at the identity the operator `Ptop + Plow` becomes a scalar coordinate operator
with smooth coefficients whose principal symbol at the chart point is the word symbol of `Ptop`;
the Euclidean interior derivative bounds then control every derivative at the identity, and
hence `lieWordAction X Q φ 1`, by the supremum of `‖φ‖` on the image of a closed coordinate
ball. -/
theorem lieGroupEllipticInteriorEstimate : LieGroupEllipticInteriorEstimateStatement.{u, v} := by
  intro E _ _ _ H _ _ _ _ n r X Ptop Plow hPtop hPlow hell Q
  classical
  let d := Module.finrank ℝ E
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) := toEuclidean
  let chart := extChartAt 𝓘(ℝ, E) (1 : H)
  let S := L.symm ⁻¹' chart.target
  let ψ := chart.symm ∘ L.symm
  let x₀ := L (chart 1)
  obtain ⟨D, V, hS, hx₀, hψ₀, hψ, hD, hcoef, hellD, haction, hexp⟩ :=
    exists_lieWordCoordinateOperator X Ptop Plow hPtop hPlow hell
  -- the Euclidean interior bounds
  obtain ⟨R, -, hRS, Cm, hCm, hbound⟩ :=
    exists_localElliptic_interior_derivative_bounds D hD hS hcoef hx₀ hellD
  have hVc : IsCompact (ψ '' closedBall x₀ R) :=
    (isCompact_closedBall x₀ R).image_of_continuousOn (hψ.continuousOn.mono hRS)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∑ w ∈ Q.coeff.support, ‖Q.coeff w‖ *
      ∑ k ∈ Finset.range (w.length + 1), ∑ W : Fin k → Fin d,
        ‖vectorFieldWordCoeff V w.toList k W x₀‖ * Cm k := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun W _ =>
        mul_nonneg (norm_nonneg _) (hCm k))
  refine ⟨ψ '' closedBall x₀ R, C, hVc, hC0, ?_⟩
  intro φ hφ hsol M hM
  have hu : ContDiffOn ℝ ∞ (φ ∘ ψ) S := contMDiffOn_iff_contDiffOn.1 (hφ.comp_contMDiffOn hψ)
  have hsolD : ∀ x ∈ S, D.action (φ ∘ ψ) x = 0 := fun x hx =>
    (haction φ hφ x hx).trans (hsol (ψ x))
  have hMb : ∀ x ∈ closedBall x₀ R, ‖(φ ∘ ψ) x‖ ≤ M := fun x hx =>
    hM (ψ x) (mem_image_of_mem ψ hx)
  have hk := hbound (φ ∘ ψ) hu hsolD M hMb
  have hw : ∀ w : FreeMonoid (Fin n), ‖(lieWordDerivative X w : (H → ℂ) → H → ℂ) φ (ψ x₀)‖ ≤
      (∑ k ∈ Finset.range (w.length + 1), ∑ W : Fin k → Fin d,
        ‖vectorFieldWordCoeff V w.toList k W x₀‖ * Cm k) * M := by
    intro w
    rw [hexp φ hφ w w.length le_rfl x₀ hx₀, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun W _ => ?_)
    rw [norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hprod : ∏ q, ‖e (W q)‖ = 1 :=
      Finset.prod_eq_one fun q _ => (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 (W q)
    rw [hprod, mul_one]
    exact hk k
  rw [← hψ₀]
  calc ‖lieWordAction X Q φ (ψ x₀)‖
      ≤ ∑ w ∈ Q.coeff.support, ‖Q.coeff w * (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ (ψ x₀)‖ := by
        rw [lieWordAction_apply]
        exact norm_sum_le _ _
    _ ≤ ∑ w ∈ Q.coeff.support, ‖Q.coeff w‖ * ((∑ k ∈ Finset.range (w.length + 1),
          ∑ W : Fin k → Fin d, ‖vectorFieldWordCoeff V w.toList k W x₀‖ * Cm k) * M) :=
        Finset.sum_le_sum fun w _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hw w) (norm_nonneg _)
    _ = C * M := by
        rw [hCdef, Finset.sum_mul (s := Q.coeff.support)]
        exact Finset.sum_congr rfl fun w _ => by ring

end Langlands.Geometry.Manifold
