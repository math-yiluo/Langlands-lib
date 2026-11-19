import Langlands.Global.RankinSelberg.RealPrincipalSeriesEvaluationReduction

/-! # A compact derivative bound for extending real Whittaker evaluations -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

variable (r : ℕ) (ds : List RealBlock)

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "K" => unitaryCompact ℝ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "V" => Automorphic.realStandardKFinite (r + 1) ds
local notation "P" => principalSeries ℝ (r + 1) (realPositionCharacter (expand ds))
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "word" => RealLocalWhittaker.iteratedRightDerivative r

/-- The submodule of twisted right-unipotent translation differences. -/
def twistedDifferences (a : ℝˣ) : Submodule ℂ P :=
  Submodule.span ℂ (Set.range fun ux : N × P =>
    translate r (expand ds) ux.1.val ux.2 - realWhittakerCharacter a ux.1.val • ux.2)

/-- A compact derivative coordinate in the supremum norm. -/
def compactDerivativeCoordinate (Xs : List Mat) : P →ₗ[ℂ] C(K, ℂ) where
  toFun x := ⟨fun k => word Xs x k,
    (RealUniformWhittaker.contMDiff_iteratedRightDerivative x.2.1 Xs).continuous.comp
      continuous_subtype_val⟩
  map_add' x y := by
    ext1 k
    exact congrFun (RealUniformWhittaker.iteratedRightDerivative_add x.2.1 y.2.1 Xs) k.val
  map_smul' c x := by
    ext1 k
    exact congrFun (RealUniformWhittaker.iteratedRightDerivative_smul x.2.1 c Xs) k.val

private theorem equivariant_iff_le_ker (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ) :
    (∀ u ∈ N, ∀ x : P,
      ℓ (translate r (expand ds) u x) = realWhittakerCharacter a u * ℓ x) ↔
    twistedDifferences r ds a ≤ ℓ.ker := by
  rw [twistedDifferences, Submodule.span_le]
  constructor
  · rintro h _ ⟨⟨u, x⟩, rfl⟩
    change translate r (expand ds) u.val x - realWhittakerCharacter a u.val • x ∈ ℓ.ker
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, h u.val u.property x, sub_self]
  · intro h u hu x
    have hx : translate r (expand ds) u x - realWhittakerCharacter a u • x ∈ ℓ.ker :=
      h ⟨(⟨u, hu⟩, x), rfl⟩
    rwa [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hx

/-- The identity evaluation bound on each representative modulo the twisted differences. -/
def HasTwistedEvaluationBound (a : ℝˣ) (B : V →ₗ[ℂ] (G → ℂ)) : Prop :=
  ∃ (m : ℕ) (Xs : Fin m → List Mat) (A : ℝ), 0 ≤ A ∧
    ∀ (f : V) (z : twistedDifferences r ds a),
      ‖B f 1‖ ≤ A * ∑ i, ‖compactDerivativeCoordinate r ds (Xs i)
        (expandedSmoothInclusion r ds f + z.val)‖

private theorem exists_bounded_factor {S E : Type*}
    [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : S →ₗ[ℂ] E) (L : S →ₗ[ℂ] ℂ) {A : ℝ}
    (h : ∀ x, ‖L x‖ ≤ A * ‖J x‖) :
    ∃ T : E →L[ℂ] ℂ, ∀ x, T (J x) = L x := by
  have hker : J.ker ≤ L.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hzero : ‖L x‖ ≤ 0 := by simpa only [hx, norm_zero, mul_zero] using h x
    exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
  let T₀ := J.ker.liftQ L hker ∘ₗ J.quotKerEquivRange.symm.toLinearMap
  have hT₀ (x : S) : T₀ (J.rangeRestrict x) = L x := by
    change J.ker.liftQ L hker (J.quotKerEquivRange.symm ⟨J x, ⟨x, rfl⟩⟩) = L x
    rw [J.quotKerEquivRange_symm_apply_image]
    rfl
  have hnorm (y : J.range) : ‖T₀ y‖ ≤ A * ‖y‖ := by
    obtain ⟨x, hx⟩ := y.property
    have hxy : J.rangeRestrict x = y := Subtype.ext hx
    rw [← hxy, hT₀]
    exact h x
  obtain ⟨T, hT, _⟩ := exists_extension_norm_eq J.range (T₀.mkContinuous A hnorm)
  exact ⟨T, fun x => (hT (J.rangeRestrict x)).trans (hT₀ x)⟩

theorem hasTwistedEvaluationBound_iff (a : ℝˣ) (B : V →ₗ[ℂ] (G → ℂ)) :
    HasTwistedEvaluationBound r ds a B ↔
    ∃ ℓ : P →ₗ[ℂ] ℂ, HasCompactDerivativeBound r (expand ds) ℓ ∧
      (∀ u ∈ N, ∀ x : P,
        ℓ (translate r (expand ds) u x) = realWhittakerCharacter a u * ℓ x) ∧
      ∀ f, ℓ (expandedSmoothInclusion r ds f) = B f 1 := by
  constructor
  · rintro ⟨m, Xs, A, hA, h⟩
    let R := twistedDifferences r ds a
    let J₀ : P →ₗ[ℂ] (Fin m → C(K, ℂ)) :=
      LinearMap.pi fun i => compactDerivativeCoordinate r ds (Xs i)
    let J : V × R →ₗ[ℂ] (Fin m → C(K, ℂ)) :=
      J₀.comp ((expandedSmoothInclusion r ds).coprod R.subtype)
    let L : V × R →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp (B.comp (LinearMap.fst ℂ V R))
    have hJL (v : V × R) : ‖L v‖ ≤ (A * (m : ℝ)) * ‖J v‖ := by
      calc
        _ ≤ A * ∑ i, ‖J v i‖ := h v.1 v.2
        _ ≤ A * ∑ _ : Fin m, ‖J v‖ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => norm_le_pi_norm (J v) i) hA
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]
    obtain ⟨T, hT⟩ := exists_bounded_factor (S := V × R) (E := Fin m → C(K, ℂ))
      J L (A := A * (m : ℝ)) hJL
    let ℓ := T.toLinearMap.comp J₀
    refine ⟨ℓ, ⟨m, Xs, ‖T‖, norm_nonneg _, ?_⟩,
      (equivariant_iff_le_ker r ds a ℓ).2 ?_, ?_⟩
    · intro x c hc
      have hci (i : Fin m) : 0 ≤ c i :=
        (norm_nonneg _).trans (hc i 1 (unitaryCompact ℝ (r + 1)).one_mem)
      have hJ₀ : ‖J₀ x‖ ≤ ∑ i, c i := by
        apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hci i)).2
        intro i
        apply ((ContinuousMap.norm_le _ (hci i)).2 fun k => hc i k.val k.property).trans
        exact Finset.single_le_sum (fun j _ => hci j) (Finset.mem_univ i)
      exact (T.le_opNorm (J₀ x)).trans (mul_le_mul_of_nonneg_left hJ₀ (norm_nonneg _))
    · intro z hz
      rw [LinearMap.mem_ker]
      have hz' := hT (0, (⟨z, hz⟩ : R))
      simpa only [J, L, ℓ, LinearMap.comp_apply, LinearMap.coprod_apply,
        LinearMap.fst_apply, map_zero, zero_add, Submodule.subtype_apply,
        LinearMap.proj_apply, Pi.zero_apply, ContinuousLinearMap.coe_coe] using hz'
    · intro f
      have hf := hT (f, (0 : R))
      simpa only [J, L, ℓ, LinearMap.comp_apply, LinearMap.coprod_apply,
        LinearMap.fst_apply, map_zero, add_zero, LinearMap.proj_apply,
        ContinuousLinearMap.coe_coe] using hf
  · rintro ⟨ℓ, ⟨m, Xs, A, hA, hℓ⟩, hψ, hEval⟩
    have hker := (equivariant_iff_le_ker r ds a ℓ).1 hψ
    refine ⟨m, Xs, A, hA, fun f z => ?_⟩
    let x := expandedSmoothInclusion r ds f + z.val
    have hz := LinearMap.mem_ker.mp (hker z.property)
    have hx : ℓ x = B f 1 := by
      change ℓ (expandedSmoothInclusion r ds f + z.val) = B f 1
      rw [map_add, hEval f, hz, add_zero]
    rw [← hx]
    exact hℓ x (fun i => ‖compactDerivativeCoordinate r ds (Xs i) x‖)
      (fun i k hk => (compactDerivativeCoordinate r ds (Xs i) x).norm_coe_le_norm ⟨k, hk⟩)

/-- The compact derivative bound modulo twisted right-unipotent differences for all
original uniform coefficient maps in the nonzero-weight case. -/
def RealUniformPrincipalSeriesTwistedBoundStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    (∃ p d, realInducedBlockAt ds p = some d ∧ d.weight ≠ 0) →
  ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
    (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealUniformWhittakerIntertwiner r ds a B → HasTwistedEvaluationBound r ds a B

/-- The uniform coefficient extension follows from the compact derivative bound modulo
twisted right-unipotent differences. -/
def RealUniformPrincipalSeriesTwistedBoundReductionStatement : Prop :=
  RealUniformPrincipalSeriesTwistedBoundStatement → RealUniformPrincipalSeriesExtensionStatement

theorem realUniformPrincipalSeriesTwistedBoundReduction :
    RealUniformPrincipalSeriesTwistedBoundReductionStatement :=
  fun h => realUniformPrincipalSeriesEvaluationReduction fun r ds hr hw a B hB =>
    (hasTwistedEvaluationBound_iff r ds a B).1 (h r ds hr hw a B hB)

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
