import Langlands.Representation.Archimedean.CompactHilbertWeight
import Langlands.Representation.Archimedean.CompactOrbitSmoothness
import Langlands.Representation.Archimedean.CompactWeightedSquare
import Langlands.Representation.Archimedean.GKKernelTraceSeparation
import Langlands.Representation.Archimedean.RealInductionStagesInduce
import Langlands.Representation.KFiniteDual

/-! # Real algebraic separation by Hilbert traces -/

noncomputable section

open MeasureTheory
open scoped TensorProduct Matrix Matrix.Norms.Operator InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (derivativeCLM toSmooth)
open Langlands.Analysis.OperatorIdeals
open InductionStages (ofUnitary toUnitary toUnits_toUnitary)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

local notation "GLR" => Langlands.GeneralLinear n ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "𝔤" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "I" => matrixModel ℝ n

section NormCompactVectors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))

/-- Inner-product invariance on the actual real maximal compact subgroup. -/
def HasUnitaryRealCompactAction : Prop :=
  ∀ (k : Kc) (x y : H), ⟪R (k : GLR) x, R (k : GLR) y⟫_ℂ = ⟪x, y⟫_ℂ

/-- A smooth norm-compact-finite vector belongs to the genuine smooth compact-finite
carrier, with its original Hilbert value as the empty word coordinate. -/
theorem exists_smoothHilbertKFinite_of_norm {x : H} (hx : IsSmoothVector I R x)
    (hK : FiniteVectors.IsFiniteVector (normCompactRepresentation Kc R) x) :
    ∃ y : smoothHilbertKFinite ℝ n R, derivativeCLM I R [] y.val = x := by
  let y := (toSmooth I R).symm ⟨x, hx⟩
  let RK := (normCompactRepresentation Kc R).comp (ofUnitary n)
  let T : (smoothHilbertCompactRepresentation ℝ n R).IntertwiningMap RK :=
    LinearMap.intertwiningMap_of_isIntertwiningMap (smoothHilbertCompactRepresentation ℝ n R)
      RK (derivativeCLM I R []).toLinearMap (fun _ _ => rfl)
  have hT : Function.Injective T :=
    fun _ _ h => (toSmooth I R).injective (Subtype.ext h)
  have hy : T y = x := rfl
  let : FiniteDimensional ℂ (FiniteVectors.orbitSpan (normCompactRepresentation Kc R) x) := hK
  have hRK : FiniteVectors.IsFiniteVector RK x := by
    apply Submodule.finiteDimensional_of_le
      (S₂ := FiniteVectors.orbitSpan (normCompactRepresentation Kc R) x)
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨ofUnitary n k, rfl⟩
  have hTy : FiniteVectors.IsFiniteVector RK (T y) := by rwa [hy]
  exact ⟨⟨y, (FiniteVectors.isFiniteVector_map_iff T hT y).mp hTy⟩, hy⟩

private theorem range_subtypeL_subset_globalizationMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n R) (P : H →L[ℂ] H)
    (hs : ∀ x : H, IsSmoothVector I R (P x))
    (hk : ∀ x : H, FiniteVectors.IsFiniteVector (normCompactRepresentation Kc R) (P x)) :
    Set.range P.toLinearMap.range.subtypeL ⊆
      Set.range (fun x => derivativeCLM I R [] (smoothHilbertGlobalizationMap ℝ n R e x)) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := x.property
  change P z = (x : H) at hz
  change (x : H) ∈ Set.range _
  rw [← hz]
  obtain ⟨y, hy⟩ := exists_smoothHilbertKFinite_of_norm n R (hs z) (hk z)
  obtain ⟨a, rfl⟩ := e.surjective y
  exact ⟨a, hy⟩

end NormCompactVectors

section Separation

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  [MeasurableSpace (unitaryCompact ℝ n)] [BorelSpace (unitaryCompact ℝ n)]
  (ν : Measure (unitaryCompact ℝ n)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
  {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
  (S : Langlands.GeneralLinear n ℝ →* (J →L[ℂ] J))
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W)
  (τ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
  (e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n R)
  (f : W ≃ₗ[ℂ] smoothHilbertKFinite ℝ n S)

local notation "j" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(Kc, GLR))
local notation "εR" => derivativeCLM I R []
local notation "εS" => derivativeCLM I S []

include ν in
/-- Equal smooth kernel traces determine the underlying irreducible real algebraic
modules for the specified Hilbert realizations. The first compact action preserves
the Hilbert inner product. -/
theorem exists_real_gkEquiv_of_sameSmoothKernelTrace
    (hR : IsContinuousRepresentation R) (hS : IsContinuousRepresentation S)
    (hadmR : IsAdmissible R Kc) (hadmS : IsAdmissible S Kc)
    (hkR : ∀ (k : K) (v : V), smoothHilbertGlobalizationMap ℝ n R e (ρ k v) =
      DerivativeSmoothVectors.representation I R (Unitary.toUnits k)
        (smoothHilbertGlobalizationMap ℝ n R e v))
    (hkS : ∀ (k : K) (w : W), smoothHilbertGlobalizationMap ℝ n S f (σ k w) =
      DerivativeSmoothVectors.representation I S (Unitary.toUnits k)
        (smoothHilbertGlobalizationMap ℝ n S f w))
    (hXR : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (v : V),
      smoothHilbertGlobalizationMap ℝ n R e (π (1 ⊗ₜ[ℝ] X) v) =
        DerivativeSmoothVectors.operator I R X (smoothHilbertGlobalizationMap ℝ n R e v))
    (hXS : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (w : W),
      smoothHilbertGlobalizationMap ℝ n S f (τ (1 ⊗ₜ[ℝ] X) w) =
        DerivativeSmoothVectors.operator I S X (smoothHilbertGlobalizationMap ℝ n S f w))
    (hExpR : HasSmoothHilbertExponentialDerivatives ℝ n R)
    (hExpS : HasSmoothHilbertExponentialDerivatives ℝ n S)
    (hgk : IsRealGKModule n ρ π) (hirrR : IsIrreducibleGKModule ρ π)
    (hirrS : IsIrreducibleGKModule σ τ) (hU : HasUnitaryRealCompactAction n R)
    (htrace : SameSmoothKernelTrace ℝ n μ R S hR hS) :
    ∃ b : V ≃ₗ[ℂ] W, (∀ (k : K) (v : V), b (ρ k v) = σ k (b v)) ∧
      ∀ (X : 𝔤) (v : V), b (π X v) = τ X (b v) := by
  let : Nontrivial V := hirrR.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let M := FiniteVectors.orbitSubrepresentation ρ v
  let : FiniteDimensional ℂ M.toSubmodule := hgk.1 v
  let b := Module.finBasis ℂ M.toSubmodule
  let vM : M.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  let u := b.equivFun vM
  let c := (Langlands.KFiniteDual.subMatrix M).comp (toUnitary n)
  have hc : Continuous c := by
    have ht : Continuous (toUnitary n) :=
      (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
    exact (Langlands.KFiniteDual.continuous_subMatrix hgk.2.1 M).comp ht
  let E := smoothHilbertGlobalizationMap ℝ n R e
  let F := smoothHilbertGlobalizationMap ℝ n S f
  let g := (εR).toLinearMap.comp E
  let i := g.comp (M.toSubmodule.subtype.comp b.equivFun.symm.toLinearMap)
  have hg_inj : Function.Injective g := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    exact (toSmooth I R).injective (Subtype.ext h)
  have hiu : i u ≠ 0 := by
    have h : i u = g v := by
      change g ((b.equivFun.symm (b.equivFun vM) : M.toSubmodule) : V) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [h, ← g.map_zero]
    exact fun hz => hv (hg_inj hz)
  have hi (k : Kc) (z : Fin (Module.finrank ℂ M.toSubmodule) → ℂ) :
      i (c k *ᵥ z) = R (k : GLR) (i z) := by
    have h := Langlands.KFiniteDual.equivFun_symm_coordRep M (toUnitary n k) z
    rw [Langlands.KFiniteDual.coordRep_apply] at h
    change b.equivFun.symm (c k *ᵥ z) =
      M.toRepresentation (toUnitary n k) (b.equivFun.symm z) at h
    change g ((b.equivFun.symm (c k *ᵥ z) : M.toSubmodule) : V) = R (k : GLR) (i z)
    rw [h]
    change εR (E (ρ (toUnitary n k) (b.equivFun.symm z : M.toSubmodule))) =
      R (k : GLR) (i z)
    rw [hkR, toUnits_toUnitary]
    rfl
  let w := compactCoefficientWeights Kc R hR i (i u)
  have hw (k x : Kc) (z : Fin (Module.finrank ℂ M.toSubmodule) → ℂ) :
      w (c k *ᵥ z) x = w z (k⁻¹ * x) :=
    compactCoefficientWeights_translate Kc R hR hU c i hi (i u) k x z
  let z₀ := compactWeightedTypeVector Kc ν c w u
  let PR := compactWeightedOrbit ν R hR j (w u)
  let PS := compactWeightedOrbit ν S hS j (w u)
  let MR := PR.toLinearMap.range
  let MS := PS.toLinearMap.range
  let hMR : FiniteDimensional ℂ MR :=
    finiteDimensional_range_compactWeightedOrbit Kc ν R hR c w hw hadmR hc u
  let hMS : FiniteDimensional ℂ MS :=
    finiteDimensional_range_compactWeightedOrbit Kc ν S hS c w hw hadmS hc u
  let : CompleteSpace MR := FiniteDimensional.complete ℂ MR
  let : CompleteSpace MS := FiniteDimensional.complete ℂ MS
  let iR : MR →L[ℂ] H := MR.subtypeL
  let iS : MS →L[ℂ] J := MS.subtypeL
  let pR : H →L[ℂ] MR := (PR.codRestrict MR (fun x => ⟨x, rfl⟩)).comp PR
  let pS : J →L[ℂ] MS := (PS.codRestrict MS (fun x => ⟨x, rfl⟩)).comp PS
  have hPR (x : H) : iR (pR x) = ∫ k, w z₀ k • R (j k) x ∂ν :=
    DFunLike.congr_fun (compactWeightedOrbit_comp_self Kc ν c w R hR hc hw u) x
  have hPS (x : J) : iS (pS x) = ∫ k, w z₀ k • S (j k) x ∂ν :=
    DFunLike.congr_fun (compactWeightedOrbit_comp_self Kc ν c w S hS hc hw u) x
  have hiR : Set.range iR ⊆ Set.range (fun x => εR (E x)) :=
    range_subtypeL_subset_globalizationMap n R e PR
      (isSmoothVector_compactWeightedOrbit_of_finiteRange ν R hR j (w u) μ hMR)
      (isFiniteVector_compactWeightedOrbit Kc ν R hR c w hw u)
  have hiS : Set.range iS ⊆ Set.range (fun x => εS (F x)) :=
    range_subtypeL_subset_globalizationMap n S f PS
      (isSmoothVector_compactWeightedOrbit_of_finiteRange ν S hS j (w u) μ hMS)
      (isFiniteVector_compactWeightedOrbit Kc ν S hS c w hw u)
  have hcomp : iR.comp pR = PR.comp PR := rfl
  have hn : hilbertCompressionTrace R iR pR 1 ≠ 0 := by
    rw [hilbertCompressionTrace, map_one]
    change operatorTrace (pR.comp iR) ≠ 0
    rw [← (operatorTrace_finite_compression iR pR).2, hcomp]
    exact operatorTrace_comp_self_ne_zero_of_selfAdjoint PR hMR
      (adjoint_compactWeightedOrbit_coefficient Kc R hR hU ν i u)
      (compactWeightedOrbit_ne_zero_of_coefficient Kc R hR ν i u hiu)
  exact exists_gkEquiv_of_sameSmoothKernelTrace ℝ n μ R S hR hS ν j (w z₀)
    iR pR iS pS E F ρ π σ τ hirrR hirrS hkR hkS hXR hXS hExpR hExpS hiR hiS hPR hPS hn htrace

end Separation

end Langlands.Archimedean
