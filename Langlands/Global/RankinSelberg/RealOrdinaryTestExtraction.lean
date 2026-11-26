import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealSmoothWhittakerEvaluation
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Extracting real ordinary tests from tensor evaluations -/

noncomputable section

open Set
open scoped Matrix.Norms.Operator SchwartzMap TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOrdinaryTestExtraction

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ArchimedeanLocal RealStandardCompactBanach

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

universe u

local notation "G[" r "]" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Std[" r "," d "]" => Automorphic.realStandardKFinite (r + 1) d
local notation "Smooth[" r "," d "]" => DerivativeSmoothVectors (matrixModel ℝ (r + 1))
  (RealStandardCompactBanach.representation (n := r + 1) d)

/-- Regard a compact-finite inducing vector as a genuine smooth standard vector. -/
def smoothOfCompact {r : ℕ} (d : List RealBlock) (f : Std[r,d]) : Smooth[r,d] :=
  (compactFiniteEquiv d f).val

/-- A given ordinary intertwiner takes each compact-finite vector to an actual model vector. -/
def coefficient {r : ℕ} {d : List RealBlock} {a : ℝˣ}
    (B : Std[r,d] →ₗ[ℂ] (G[r] → ℂ)) (hB : IsRealWhittakerIntertwiner r d a B) (f : Std[r,d]) :
    realWhittakerModel r d a :=
  ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩

private theorem exists_ne_zero_on_dense_pure {A X : Type*} [TopologicalSpace X]
    {T : Type u} [TopologicalSpace T] [AddCommGroup T] [Module ℂ T]
    (j : A → X) (hj : DenseRange j) (pure : X → T) (hpure : Continuous pure)
    (hSpan : Dense (Submodule.span ℂ (range pure) : Set T)) (L : T →L[ℂ] ℂ)
    (hL : ∃ t, L t ≠ 0) : ∃ x, L (pure (j x)) ≠ 0 := by
  by_contra! hz
  have hvanish : (fun x => L (pure x)) = fun _ => 0 :=
    hj.equalizer (L.continuous.comp hpure) continuous_const (funext hz)
  have hle : Submodule.span ℂ (range pure) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact congrFun hvanish x
  obtain ⟨t, ht⟩ := hL
  apply ht
  have hc : IsClosed (L.ker : Set T) := L.isClosed_ker
  exact hc.closure_subset_iff.mpr hle (hSpan t)

/-- A nonzero continuous normalized evaluation on a space with dense smooth pure
pair span gives pointwise coverage by ordinary compact-finite unequal-rank tests. -/
def RealUnequalSmoothEvaluationExtractionStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (d e : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (B : Std[r,d] →ₗ[ℂ] (G[r] → ℂ)) (C : Std[t,e] →ₗ[ℂ] (G[t] → ℂ))
    (hB : IsRealWhittakerIntertwiner r d a B) (hC : IsRealWhittakerIntertwiner t e (-a) C)
    (T : Type u) [TopologicalSpace T] [AddCommGroup T] [Module ℂ T]
    (pure : Smooth[r,d] × Smooth[t,e] → T) (L : ℂ → T →L[ℂ] ℂ),
    Continuous pure → Dense (Submodule.span ℂ (range pure) : Set T) →
    (∀ s, ∃ z, L s z ≠ 0) →
    (∀ (f : Std[r,d]) (g : Std[t,e]),
      ∃ N : OrdinaryIntegralNormalization
        (realOrdinaryUnequalTest h d e a D (coefficient B hB f, coefficient C hC g))
        (fun s => ((realPairLFactor d e).denominator s)⁻¹),
        ∀ s, N.value s = L s (pure (smoothOfCompact d f, smoothOfCompact e g))) →
    HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e)

theorem realUnequalSmoothEvaluationExtraction : RealUnequalSmoothEvaluationExtractionStatement.{u} := by
  intro r t h d e a D B C hB hC T _ _ _ pure L hp hSpan hL hN s
  obtain ⟨⟨f, g⟩, hfg⟩ := exists_ne_zero_on_dense_pure (Prod.map (smoothOfCompact d) (smoothOfCompact e))
    ((denseRange_compactFiniteEquiv d).prodMap (denseRange_compactFiniteEquiv e)) pure hp hSpan (L s) (hL s)
  obtain ⟨N, hN⟩ := hN f g
  exact ⟨(coefficient B hB f, coefficient C hC g), N, (hN s).symm ▸ hfg⟩

/-- In equal rank the same extraction keeps the Schwartz row as a third smooth input. -/
def RealEqualSmoothEvaluationExtractionStatement : Prop :=
  ∀ (r : ℕ) (d e : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (B : Std[r,d] →ₗ[ℂ] (G[r] → ℂ)) (C : Std[r,e] →ₗ[ℂ] (G[r] → ℂ))
    (hB : IsRealWhittakerIntertwiner r d a B) (hC : IsRealWhittakerIntertwiner r e (-a) C)
    (T : Type u) [TopologicalSpace T] [AddCommGroup T] [Module ℂ T]
    (pure : Smooth[r,d] × Smooth[r,e] × 𝓢((Fin (r + 1) → ℝ), ℂ) → T) (L : ℂ → T →L[ℂ] ℂ),
    Continuous pure → Dense (Submodule.span ℂ (range pure) : Set T) →
    (∀ s, ∃ z, L s z ≠ 0) →
    (∀ (f : Std[r,d]) (g : Std[r,e]) (Φ : 𝓢((Fin (r + 1) → ℝ), ℂ)),
      ∃ N : OrdinaryIntegralNormalization
        (realOrdinaryEqualTest r d e a D (coefficient B hB f, coefficient C hC g, Φ))
        (fun s => ((realPairLFactor d e).denominator s)⁻¹),
        ∀ s, N.value s = L s (pure (smoothOfCompact d f, smoothOfCompact e g, Φ))) →
    HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e)

theorem realEqualSmoothEvaluationExtraction : RealEqualSmoothEvaluationExtractionStatement.{u} := by
  intro r d e a D B C hB hC T _ _ _ pure L hp hSpan hL hN s
  obtain ⟨⟨f, g, Φ⟩, hfg⟩ := exists_ne_zero_on_dense_pure
    (Prod.map (smoothOfCompact d) (Prod.map (smoothOfCompact e) id))
    ((denseRange_compactFiniteEquiv d).prodMap ((denseRange_compactFiniteEquiv e).prodMap denseRange_id))
    pure hp hSpan (L s) (hL s)
  obtain ⟨N, hN⟩ := hN f g Φ
  exact ⟨(coefficient B hB f, coefficient C hC g, Φ), N, (hN s).symm ▸ hfg⟩

section Algebraic

variable {A B C Test : Type*}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
variable (I : Test → ℂ → ℂ) (L : ReciprocalEntire)

/-- A constant algebraic tensor normalization gives a finite sum of pure tests. -/
theorem finiteSum_of_algebraicPair (test : A → B → Test) (F : A ⊗[ℂ] B →ₗ[ℂ] (ℂ → ℂ))
    (hF : ∀ x y, ∃ N : OrdinaryIntegralNormalization (I (test x y)) (fun s => (L.denominator s)⁻¹),
      ∀ s, N.value s = F (x ⊗ₜ[ℂ] y) s)
    (hOne : ∃ z, ∀ s, F z s = 1) : HasFiniteOrdinaryNormalizationSum I L := by
  classical
  obtain ⟨z, hz⟩ := hOne
  obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  choose N hN using fun j : Fin n => hF (x j) (y j)
  refine ⟨n, fun j => test (x j) (y j), N, fun s => ?_⟩
  simpa only [map_sum, Finset.sum_apply, hN] using hz s

/-- A constant algebraic tensor normalization with a third factor likewise
expands into a finite sum of pure tests. -/
theorem finiteSum_of_algebraicTriple [AddCommGroup C] [Module ℂ C]
    (test : A → B → C → Test) (F : A ⊗[ℂ] (B ⊗[ℂ] C) →ₗ[ℂ] (ℂ → ℂ))
    (hF : ∀ x y w, ∃ N : OrdinaryIntegralNormalization (I (test x y w)) (fun s => (L.denominator s)⁻¹),
      ∀ s, N.value s = F (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] w)) s)
    (hOne : ∃ z, ∀ s, F z s = 1) : HasFiniteOrdinaryNormalizationSum I L := by
  classical
  obtain ⟨z, hz⟩ := hOne
  obtain ⟨n, x, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  choose m y w hw using fun j : Fin n => TensorProduct.exists_sum_tmul_eq (b j)
  have hTensor : (∑ j, x j ⊗ₜ[ℂ] b j) = ∑ j, ∑ k, x j ⊗ₜ[ℂ] (y j k ⊗ₜ[ℂ] w j k) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j, TensorProduct.tmul_sum]
  rw [hTensor] at hz
  let J := Σ j : Fin n, Fin (m j)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let i (j : J) := test (x j.1) (y j.1 j.2) (w j.1 j.2)
  choose N hN using fun j : J => hF (x j.1) (y j.1 j.2) (w j.1 j.2)
  refine ⟨Fintype.card J, fun j => i (e j), fun j => N (e j), fun s => ?_⟩
  calc
    _ = ∑ j : J, (N j).value s := Equiv.sum_comp e _
    _ = ∑ j : Fin n, ∑ k : Fin (m j), F (x j ⊗ₜ[ℂ] (y j k ⊗ₜ[ℂ] w j k)) s := by
      simp only [hN, Fintype.sum_sigma, J]
    _ = 1 := by simpa only [map_sum, Finset.sum_apply] using hz s

end Algebraic

/-- The smooth-model extraction principles for the two real ordinary test families. -/
def RealOrdinarySmoothEvaluationExtractionStatement : Prop :=
  RealUnequalSmoothEvaluationExtractionStatement.{u} ∧ RealEqualSmoothEvaluationExtractionStatement.{u}

theorem realOrdinarySmoothEvaluationExtraction : RealOrdinarySmoothEvaluationExtractionStatement.{u} :=
  ⟨realUnequalSmoothEvaluationExtraction, realEqualSmoothEvaluationExtraction⟩

end Langlands.Global.RankinSelbergGlobal.RealOrdinaryTestExtraction
