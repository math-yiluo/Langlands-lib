import Langlands.Algebra.TensorCubeScalarDefect
import Langlands.LinearAlgebra.GaloisLineDescent

/-! # Actual fixed-field splitting from restricted scalar defects -/

noncomputable section
universe u
open Matrix
open scoped TensorProduct

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
  [Ring A] [Algebra k A]

local instance intermediateTensorRing (F : IntermediateField k L) : Ring (F ⊗[k] A) :=
  Algebra.TensorProduct.instRing
local instance intermediateTensorAlgebra (F : IntermediateField k L) : Algebra F (F ⊗[k] A) :=
  Algebra.TensorProduct.leftAlgebra
local instance nestedIntermediateTensorRing (F : IntermediateField k L) :
    Ring (L ⊗[F] (F ⊗[k] A)) := Algebra.TensorProduct.instRing


/-- Cancellation of two successive scalar extensions for a possibly
noncommutative algebra. -/
def intermediateScalarInterchange (F : IntermediateField k L) :
    L ⊗[F] (F ⊗[k] A) ≃ₐ[L] L ⊗[k] A :=
  (Algebra.TensorProduct.assoc k F L L F A).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid F L L)
      (AlgEquiv.refl : A ≃ₐ[k] A))

@[simp] theorem intermediateScalarInterchange_tmul (F : IntermediateField k L)
    (l : L) (f : F) (a : A) :
    intermediateScalarInterchange F (l ⊗ₜ[F] (f ⊗ₜ[k] a)) = (f • l) ⊗ₜ[k] a := by
  simp [intermediateScalarInterchange, Algebra.TensorProduct.congr_apply]

/-- Coefficient actions commute with cancellation of successive scalar extensions. -/
theorem intermediateScalarInterchange_coefficientMap (F : IntermediateField k L)
    (σ : L ≃ₐ[F] L) (X : L ⊗[F] (F ⊗[k] A)) :
    intermediateScalarInterchange F (tensorCoefficientMap σ X) =
      tensorCoefficientMap (σ.restrictScalars k) (intermediateScalarInterchange F X) := by
  induction X with
  | tmul l y =>
    induction y with
    | tmul f a =>
      simp only [tensorCoefficientMap_tmul, intermediateScalarInterchange_tmul]
      congr 1
      change (f : L) * σ l = σ ((f : L) * l)
      have hf : σ (f : L) = (f : L) := σ.commutes f
      rw [map_mul, hf]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add X Y hX hY => simp only [map_add, hX, hY]

/-- The supplied actual chart after replacing the ground field by an
intermediate field. -/
def intermediateSplittingChart (F : IntermediateField k L) {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    L ⊗[F] (F ⊗[k] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L :=
  (intermediateScalarInterchange F).trans e

/-- The actual intermediate-field chart restricts the original coefficient action. -/
theorem intermediateSplittingChart_action (F : IntermediateField k L) {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (σ : L ≃ₐ[F] L) (X : Matrix (Fin n) (Fin n) L) :
    (splittingChartAction (intermediateSplittingChart F e)).act σ X =
      (splittingChartAction e).act (σ.restrictScalars k) X := by
  obtain ⟨Y, rfl⟩ := (intermediateSplittingChart F e).surjective X
  change (splittingChartAction (intermediateSplittingChart F e)).act σ
    ((intermediateSplittingChart F e) Y) =
    (splittingChartAction e).act (σ.restrictScalars k) (e (intermediateScalarInterchange F Y))
  rw [splittingChartAction_apply, splittingChartAction_apply]
  change e (intermediateScalarInterchange F (tensorCoefficientMap σ Y)) = _
  rw [intermediateScalarInterchange_coefficientMap]

attribute [local instance] SemilinearGaloisAction.coefficientGLAction

variable [FiniteDimensional k L]

/-- A cochain on an actual automorphism subgroup transfers to its actual
fixed-field Galois group with the same coefficient action. -/
theorem scalarDefect_isCoboundary_on_fixedField {n : ℕ}
    (ρ : SemilinearGaloisAction k L (Matrix (Fin n) (Fin n) L))
    (H : Subgroup (L ≃ₐ[k] L))
    (hc : Langlands.ScalarTwoCocycle.IsCoboundary (Γ := H)
      (fun σ τ => ρ.scalarDefect σ.val τ.val)) :
    Langlands.ScalarTwoCocycle.IsCoboundary
      (fun (σ τ : L ≃ₐ[IntermediateField.fixedField H] L) =>
        ρ.scalarDefect (σ.restrictScalars k) (τ.restrictScalars k)) := by
  let e := IntermediateField.subgroupEquivAlgEquiv H
  have he (σ : L ≃ₐ[IntermediateField.fixedField H] L) :
      (e.symm σ).val = σ.restrictScalars k := by
    ext l
    rw [← Langlands.LinearAlgebra.GaloisLineDescent.subgroupEquivAlgEquiv_apply,
      e.apply_symm_apply]
    rfl
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun σ => b (e.symm σ), fun σ τ => ?_⟩
  have h := hb (e.symm σ) (e.symm τ)
  change ρ.scalarDefect (e.symm σ).val (e.symm τ).val =
    b (e.symm σ) * ((e.symm σ) • b (e.symm τ)) * (b (e.symm σ * e.symm τ))⁻¹ at h
  rw [he, he, ← map_mul] at h
  change ρ.scalarDefect (σ.restrictScalars k) (τ.restrictScalars k) =
    b (e.symm σ) * ((e.symm σ).val • b (e.symm τ)) * (b (e.symm (σ * τ)))⁻¹ at h
  rw [he] at h
  exact h

/-- A cochain trivializing the restricted actual chart defect gives a cochain
for the actual intermediate-field chart's chosen defect. -/
theorem intermediateSplittingChart_scalarDefect_isCoboundary {n : ℕ} [NeZero n]
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (H : Subgroup (L ≃ₐ[k] L))
    (hc : Langlands.ScalarTwoCocycle.IsCoboundary (Γ := H)
      (fun σ τ => (splittingChartAction e).scalarDefect σ.val τ.val)) :
    Langlands.ScalarTwoCocycle.IsCoboundary
      (splittingChartAction (intermediateSplittingChart (IntermediateField.fixedField H) e)).scalarDefect := by
  let F := IntermediateField.fixedField H
  let ρ := splittingChartAction e
  let θ := splittingChartAction (intermediateSplittingChart F e)
  let x : (L ≃ₐ[F] L) → GL (Fin n) L := fun σ => ρ.innerMatrix (σ.restrictScalars k)
  let c : (L ≃ₐ[F] L) → (L ≃ₐ[F] L) → Lˣ :=
    fun σ τ => ρ.scalarDefect (σ.restrictScalars k) (τ.restrictScalars k)
  have hact (σ : L ≃ₐ[F] L) (X : Matrix (Fin n) (Fin n) L) :
      θ.act σ X = (x σ : Matrix (Fin n) (Fin n) L) * X.map σ *
        (((x σ)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [intermediateSplittingChart_action, ρ.act_eq_innerMatrix]
    rfl
  have hlift (σ τ : L ≃ₐ[F] L) : x σ * (σ • x τ) =
      GeneralLinearGroup.scalar (Fin n) (c σ τ) * x (σ * τ) := by
    exact ρ.innerMatrix_mul (σ.restrictScalars k) (τ.restrictScalars k)
  apply SemilinearGaloisAction.isCoboundary_of_same_matrix_conjugation
    θ.innerMatrix x θ.scalarDefect c θ.innerMatrix_mul hlift
    _ (scalarDefect_isCoboundary_on_fixedField ρ H hc)
  intro σ X
  let Y := X.map σ.symm
  have h := (θ.act_eq_innerMatrix σ Y).symm.trans (hact σ Y)
  have hmap : Y.map σ = X := by
    ext i j
    exact σ.apply_symm_apply (X i j)
  rw [hmap] at h
  exact h

variable [IsGalois k L] [FiniteDimensional k A]

/-- Triviality on an actual automorphism subgroup constructs an actual splitting
over its fixed field. -/
theorem split_over_fixedField_of_scalarDefect_isCoboundary {n : ℕ} [NeZero n]
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (H : Subgroup (L ≃ₐ[k] L))
    (hc : Langlands.ScalarTwoCocycle.IsCoboundary (Γ := H)
      (fun σ τ => (splittingChartAction e).scalarDefect σ.val τ.val)) :
    Nonempty ((IntermediateField.fixedField H) ⊗[k] A ≃ₐ[IntermediateField.fixedField H]
      Matrix (Fin n) (Fin n) (IntermediateField.fixedField H)) :=
  split_of_splittingChart_scalarDefect_isCoboundary
    (intermediateSplittingChart (IntermediateField.fixedField H) e)
    (intermediateSplittingChart_scalarDefect_isCoboundary e H hc)

/-- A split power with exponent prime to a subgroup's order already splits the
original algebra over the subgroup's actual fixed field. -/
theorem split_over_fixedField_of_coprime_scalarDefect_power {n : ℕ} [NeZero n]
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (H : Subgroup (L ≃ₐ[k] L)) (m : ℕ) (hm : m.Coprime (Nat.card H))
    (hpow : Langlands.ScalarTwoCocycle.IsCoboundary
      (fun σ τ => (splittingChartAction e).scalarDefect σ τ ^ m)) :
    Nonempty ((IntermediateField.fixedField H) ⊗[k] A ≃ₐ[IntermediateField.fixedField H]
      Matrix (Fin n) (Fin n) (IntermediateField.fixedField H)) := by
  let := Fintype.ofFinite H
  have htwo : Langlands.ScalarTwoCocycle.IsTwoCocycle (Γ := H)
      (fun σ τ => (splittingChartAction e).scalarDefect σ.val τ.val) := by
    intro σ τ υ
    exact (splittingChartAction e).scalarDefect_isTwoCocycle σ.val τ.val υ.val
  have hpower : Langlands.ScalarTwoCocycle.IsCoboundary (Γ := H)
      (fun σ τ => (splittingChartAction e).scalarDefect σ.val τ.val ^ m) := by
    obtain ⟨b, hb⟩ := hpow
    exact ⟨fun σ => b σ.val, fun σ τ => hb σ.val τ.val⟩
  apply split_over_fixedField_of_scalarDefect_isCoboundary e H
  apply Langlands.ScalarTwoCocycle.isCoboundary_of_coprime_card htwo _ hpower
  simpa only [Nat.card_eq_fintype_card] using hm

end Langlands.CentralSimple
