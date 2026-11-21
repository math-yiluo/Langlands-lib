import Langlands.Automorphic.GeneralLinearAutomorphicTaylorMap
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Global.EisensteinMeromorphicDetection

/-! # An injective one-parameter normalization of continued Eisenstein forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions UniformGrowthFrechetSpace

/-- The part of the complex line that stays inside the normalization ball. -/
def normalizedAutomorphicLineDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z t₁ : E) (r : ℝ) : Set ℂ :=
  (AffineMap.lineMap (k := ℂ) z t₁) ⁻¹' Metric.ball z r

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance : IsAffine (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, n])
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
  (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n])))

local notation "Growth" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "Adeles" => AdelicGroupPoints F GL[F, n]
local notation "Kinf" => generalLinearStandardInfiniteCompact F n
local notation "underlying" => UniformGrowthFrechetSpace.toFun F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "isAut" => IsAutomorphicFunctionOn F GL[F, n] hsmooth hcalc
  (AdelicGroupPoints.rationalSubgroup F GL[F, n]) Kinf rho

include hG hL in
/-- A common normalization has a complex line through the specialization and
an injective regular parameter. On it every Taylor order gives a linear map
into the actual stable automorphic module. -/
theorem exists_normalizedAutomorphicLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m : ℕ} (z : E) (r : ℝ) (hr : 0 < r) (f : Fin m → E → Adeles → ℂ)
    (hF : HasLocalHolomorphicNumerators univ (continuedLinearCombination f))
    {t₀ : E} (hreg : t₀ ∈ regularParameterSet univ (continuedLinearCombination f))
    (hinj : Function.Injective (continuedLinearCombination f t₀))
    (a : E → ℂ) (J : E → (Fin m → ℂ) →ₗ[ℂ] Growth)
    (hJ : ∀ c (test : Growth →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => test (J t c)) (Metric.ball z r))
    (V : Set E) (hVo : IsOpen V) (hVball : V ⊆ Metric.ball z r) (hcl : Metric.ball z r ⊆ closure V)
    (hregular : ∀ t ∈ V, a t ≠ 0 ∧ ∀ c, underlying (J t c) = a t • continuedLinearCombination f t c)
    (hautomorphic : ∀ j t, t ∈ V → isAut (f j t)) :
    ∃ t₁ ∈ V,
      let line := AffineMap.lineMap (k := ℂ) z t₁
      let U := normalizedAutomorphicLineDomain z t₁ r
      let O := line ⁻¹' V
      IsOpen U ∧ IsPreconnected U ∧ (0 : ℂ) ∈ U ∧
      IsOpen O ∧ (1 : ℂ) ∈ O ∧ O ⊆ U ∧
      Function.Injective (fun c => underlying (J t₁ c)) ∧
      (∀ c (test : Growth →L[ℂ] ℂ), DifferentiableOn ℂ (fun s => test (J (line s) c)) U) ∧
      (∀ s ∈ O, ∀ c, isAut (underlying (J (line s) c))) ∧
      ∃ coefficient : ℕ → (Fin m → ℂ) →ₗ[ℂ] StableAutomorphicFunctions F n,
        ∀ k c x, stableGeneralLinearEvaluation F n (coefficient k c) x =
          iteratedDeriv k (fun s : ℂ => underlying (J (line s) c) x) 0 / (k.factorial : ℂ) := by
  have hne : V.Nonempty := closure_nonempty_iff.mp ⟨z, hcl (Metric.mem_ball_self hr)⟩
  obtain ⟨t₁, ht₁, htinj⟩ := hF.exists_injective_of_open isOpen_univ isPreconnected_univ
    (mem_univ t₀) hreg hinj hVo (subset_univ _) hne
  let line := AffineMap.lineMap (k := ℂ) z t₁
  let U := normalizedAutomorphicLineDomain z t₁ r
  let O := line ⁻¹' V
  have hd : Differentiable ℂ line := by
    intro s
    change DifferentiableAt ℂ (fun w : ℂ => AffineMap.lineMap z t₁ w) s
    simp_rw [AffineMap.lineMap_apply_module']
    exact (differentiableAt_id.smul (differentiableAt_const (t₁ - z))).add_const _
  have hUo : IsOpen U := Metric.isOpen_ball.preimage hd.continuous
  have hconv : Convex ℝ U := by
    let linear : ℂ →ₗ[ℝ] E := ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (t₁ - z)).restrictScalars ℝ
    have hEq : U = linear ⁻¹' ((fun x : E => x + z) ⁻¹' Metric.ball z r) := by
      ext s
      change line s ∈ Metric.ball z r ↔ s • (t₁ - z) + z ∈ Metric.ball z r
      rw [show line s = s • (t₁ - z) + z from AffineMap.lineMap_apply_module' z t₁ s]
    rw [hEq]
    exact ((convex_ball z r).translate_preimage_left z).linear_preimage linear
  have hU : IsPreconnected U := hconv.isPreconnected
  have hzU : (0 : ℂ) ∈ U := by
    simpa [U, normalizedAutomorphicLineDomain] using Metric.mem_ball_self (x := z) hr
  have hO : IsOpen O := hVo.preimage hd.continuous
  have h1 : (1 : ℂ) ∈ O := by simpa [O, line] using ht₁.1
  have hOU : O ⊆ U := fun _ hs => hVball hs
  have hJi : Function.Injective (fun c => underlying (J t₁ c)) := by
    obtain ⟨ha, heq⟩ := hregular t₁ ht₁.1
    intro c b hcb
    change underlying (J t₁ c) = underlying (J t₁ b) at hcb
    rw [heq c, heq b] at hcb
    apply htinj
    simpa [smul_smul, inv_mul_cancel₀ ha] using congrArg (fun g : Adeles → ℂ => (a t₁)⁻¹ • g) hcb
  have hWeak (c : Fin m → ℂ) (test : Growth →L[ℂ] ℂ) :
      DifferentiableOn ℂ (fun s => test (J (line s) c)) U :=
    (hJ c test).comp hd.differentiableOn fun _ hs => hs
  have hform (s : ℂ) (hs : s ∈ O) (c : Fin m → ℂ) : isAut (underlying (J (line s) c)) := by
    let hK := generalLinearStandardInfiniteCompact_isMaximalCompact F n
    let forms := rationalAutomorphicFunctionSubmodule F GL[F, n] hsmooth hcalc rho Kinf hG hrho hK hN
    have hmem (g : Adeles → ℂ) : g ∈ forms ↔ isAut g :=
      mem_rationalAutomorphicFunctionSubmodule F GL[F, n] hsmooth hcalc rho Kinf hG hrho hK hN g
    apply (hmem _).mp
    rw [(hregular (line s) hs).2 c, continuedLinearCombination_apply]
    exact forms.smul_mem _ (forms.sum_mem fun j _ => forms.smul_mem _
      ((hmem _).mpr (hautomorphic j (line s) hs)))
  refine ⟨t₁, ht₁.1, hUo, hU, hzU, hO, h1, hOU, hJi, hWeak, hform, ?_⟩
  let coefficient (k : ℕ) := stableGeneralLinearTaylorMap F n rho hsmooth hcalc hN hrho hG R L hL
    hU hUo hO hOU ⟨1, h1⟩ (fun s => J (line s)) hWeak hform ⟨0, hzU⟩ k
  exact ⟨coefficient, fun k c x => evaluate_stableGeneralLinearTaylorMap F n rho hsmooth hcalc hN hrho
    hG R L hL hU hUo hO hOU ⟨1, h1⟩ (fun s => J (line s)) hWeak hform ⟨0, hzU⟩ k c x⟩

end Langlands.Global.EisensteinJet
