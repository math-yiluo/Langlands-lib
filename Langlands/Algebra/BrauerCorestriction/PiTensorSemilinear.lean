import Mathlib

/-!
# Semilinear maps of finite tensor products

Given a ring homomorphism `φ : R →+* R'` and a family of `φ`-semilinear maps `F i : s i → t i`,
this file constructs the `φ`-semilinear map `⨂[R] i, s i → ⨂[R'] i, t i` sending
`⨂ i, f i` to `⨂ i, F i (f i)`. When the `F i` are multiplicative maps of algebras, so is the
tensor product map. Reindexing of a tensor product of algebras is multiplicative.
-/

universe u₁ u₂ u₃ u₄ u₅

open PiTensorProduct Function
open scoped TensorProduct

namespace Langlands.PiTensorSemilinear

section Module

variable {ι : Type u₁} {R : Type u₂} {R' : Type u₃} [CommSemiring R] [CommSemiring R']
variable (φ : R →+* R')
variable {s : ι → Type u₄} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {t : ι → Type u₅} [∀ i, AddCommMonoid (t i)] [∀ i, Module R' (t i)]

private theorem apply_update_eq [DecidableEq ι] (F : ∀ i, s i →ₛₗ[φ] t i) (f : ∀ i, s i)
    (i : ι) (m : s i) :
    (fun j => F j (update f i m j)) = update (fun j => F j (f j)) i (F i m) :=
  funext fun j => apply_update (fun j => F j) f i m j

/-- The `φ`-semilinear map of tensor products induced by a family of `φ`-semilinear maps. -/
noncomputable def piTensorSemilinear (F : ∀ i, s i →ₛₗ[φ] t i) :
    (⨂[R] i, s i) →ₛₗ[φ] (⨂[R'] i, t i) where
  toFun := liftAddHom (fun p : R × Π i, s i => tprodCoeff R' (φ p.1) (fun i => F i (p.2 i)))
    (fun r f i hf => zero_tprodCoeff' _ _ i (by simp [hf]))
    (fun f => by simp only [map_zero, zero_tprodCoeff])
    (fun r f i m₁ m₂ => by
      simp only [apply_update_eq, map_add, add_tprodCoeff])
    (fun r r' f => by simp only [map_add, add_tprodCoeff'])
    (fun r f i r' => by
      simp only
      rw [apply_update_eq, map_smulₛₗ, map_mul]
      exact smul_tprodCoeff_aux (φ r) (fun j => F j (f j)) i (φ r'))
  map_add' := map_add _
  map_smul' r x := by
    induction x using PiTensorProduct.induction_on' with
    | tprodCoeff z f =>
      change tprodCoeff R' (φ (r • z)) _ = φ r • tprodCoeff R' (φ z) _
      rw [smul_tprodCoeff', smul_eq_mul, smul_eq_mul, map_mul]
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      rw [hx, hy]

variable {φ}

theorem piTensorSemilinear_tprodCoeff (F : ∀ i, s i →ₛₗ[φ] t i) (z : R) (f : ∀ i, s i) :
    piTensorSemilinear φ F (tprodCoeff R z f) = tprodCoeff R' (φ z) (fun i => F i (f i)) :=
  rfl

@[simp]
theorem piTensorSemilinear_tprod (F : ∀ i, s i →ₛₗ[φ] t i) (f : ∀ i, s i) :
    piTensorSemilinear φ F (tprod R f) = tprod R' (fun i => F i (f i)) := by
  change piTensorSemilinear φ F (tprodCoeff R 1 f) = tprodCoeff R' 1 _
  rw [piTensorSemilinear_tprodCoeff, map_one]

/-- Two semilinear maps out of a tensor product agreeing on pure tensors are equal. -/
theorem semilinear_ext {M : Type*} [AddCommMonoid M] [Module R' M]
    {G₁ G₂ : (⨂[R] i, s i) →ₛₗ[φ] M} (h : ∀ f : ∀ i, s i, G₁ (tprod R f) = G₂ (tprod R f)) :
    G₁ = G₂ := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [map_smulₛₗ, map_smulₛₗ, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [∀ i, Module R' (t i)] in
theorem piTensorSemilinear_id (F : ∀ i, s i →ₗ[R] s i) (hF : ∀ i x, F i x = x) :
    piTensorSemilinear (RingHom.id R) F = LinearMap.id := by
  refine semilinear_ext fun f => ?_
  rw [piTensorSemilinear_tprod, LinearMap.id_apply]
  exact congrArg _ (funext fun i => hF i (f i))

theorem piTensorSemilinear_comp {R'' : Type*} [CommSemiring R''] {ψ : R' →+* R''}
    {χ : R →+* R''} [RingHomCompTriple φ ψ χ]
    {u : ι → Type*} [∀ i, AddCommMonoid (u i)] [∀ i, Module R'' (u i)]
    (G : ∀ i, t i →ₛₗ[ψ] u i) (F : ∀ i, s i →ₛₗ[φ] t i) (H : ∀ i, s i →ₛₗ[χ] u i)
    (hH : ∀ i x, H i x = G i (F i x)) :
    (piTensorSemilinear ψ G).comp (piTensorSemilinear φ F) = piTensorSemilinear χ H := by
  refine semilinear_ext fun f => ?_
  rw [LinearMap.comp_apply, piTensorSemilinear_tprod, piTensorSemilinear_tprod,
    piTensorSemilinear_tprod]
  exact congrArg _ (funext fun i => (hH i (f i)).symm)

end Module

section Algebra

variable {ι : Type u₁} {R : Type u₂} {R' : Type u₃} [CommSemiring R] [CommSemiring R']
variable {φ : R →+* R'}
variable {s : ι → Type u₄} [∀ i, Semiring (s i)] [∀ i, Algebra R (s i)]
variable {t : ι → Type u₅} [∀ i, Semiring (t i)] [∀ i, Algebra R' (t i)]

theorem piTensorSemilinear_one (F : ∀ i, s i →ₛₗ[φ] t i) (hF : ∀ i, F i 1 = 1) :
    piTensorSemilinear φ F 1 = 1 := by
  rw [PiTensorProduct.one_def, piTensorSemilinear_tprod, PiTensorProduct.one_def]
  exact congrArg _ (funext hF)

theorem piTensorSemilinear_mul (F : ∀ i, s i →ₛₗ[φ] t i)
    (hF : ∀ i x y, F i (x * y) = F i x * F i y) (x y : ⨂[R] i, s i) :
    piTensorSemilinear φ F (x * y) = piTensorSemilinear φ F x * piTensorSemilinear φ F y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' g =>
      rw [smul_tprod_mul_smul_tprod, map_smulₛₗ, map_smulₛₗ, map_smulₛₗ,
        piTensorSemilinear_tprod, piTensorSemilinear_tprod, piTensorSemilinear_tprod,
        smul_tprod_mul_smul_tprod, map_mul]
      exact congrArg _ (congrArg _ (funext fun i => hF i (f i) (g i)))
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]

/-- The ring homomorphism underlying `piTensorSemilinear` for multiplicative maps. -/
noncomputable def piTensorRingHom (F : ∀ i, s i →ₛₗ[φ] t i) (hF₁ : ∀ i, F i 1 = 1)
    (hF : ∀ i x y, F i (x * y) = F i x * F i y) :
    (⨂[R] i, s i) →+* (⨂[R'] i, t i) where
  toFun := piTensorSemilinear φ F
  map_one' := piTensorSemilinear_one F hF₁
  map_mul' := piTensorSemilinear_mul F hF
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
theorem piTensorRingHom_apply (F : ∀ i, s i →ₛₗ[φ] t i) (hF₁ : ∀ i, F i 1 = 1)
    (hF : ∀ i x y, F i (x * y) = F i x * F i y) (x : ⨂[R] i, s i) :
    piTensorRingHom F hF₁ hF x = piTensorSemilinear φ F x :=
  rfl

variable (R) in
/-- Reindexing a tensor product of algebras preserves multiplication. -/
theorem reindex_mul {ι₂ : Type*} (e : ι ≃ ι₂) (x y : ⨂[R] i, s i) :
    reindex R s e (x * y) = reindex R s e x * reindex R s e y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' g =>
      rw [smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul, reindex_tprod,
        reindex_tprod, reindex_tprod, smul_tprod_mul_smul_tprod]
      rfl
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]

variable (R) in
theorem reindex_one {ι₂ : Type*} (e : ι ≃ ι₂) :
    reindex R s e 1 = 1 := by
  rw [PiTensorProduct.one_def, reindex_tprod, PiTensorProduct.one_def]
  rfl

end Algebra

end Langlands.PiTensorSemilinear
