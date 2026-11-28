import Langlands.GroupScheme.Quaternionic.Involution
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Multiplication of unitary embedding twists by norms -/

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic
open scoped TensorProduct

private def involutionUnit {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (τ : FirstKindInvolution R A) (u : Aˣ) : Aˣ where
  val := τ u
  inv := τ (↑u⁻¹)
  val_inv := by rw [← τ.map_mul, Units.inv_mul, τ.map_one]
  inv_val := by rw [← τ.map_mul, Units.mul_inv, τ.map_one]

/-- The unitary solution attached to a twist persists on multiplication by a norm
from the source algebra with involution. -/
theorem exists_unitarySolution_mul_norm {R P B : Type*} [CommRing R] [CommRing P]
    [Ring B] [Algebra R P] [Algebra R B] (σ : FirstKindInvolution R P)
    (τ : FirstKindInvolution R B) (ε : P →ₐ[R] B) (g : Bˣ)
    (hε : ∀ x : P, τ (ε x) = (g : B) * ε (σ x) * ↑g⁻¹)
    {a : P} {h : Bˣ} (ha : (g : B) * ε a = (h : B) * τ h) (p : Pˣ) :
    ∃ h' : Bˣ, (g : B) * ε (a * ((p : P) * σ p)) = (h' : B) * τ h' := by
  refine ⟨involutionUnit τ (Units.map ε.toMonoidHom p) * h, ?_⟩
  change (g : B) * ε (a * ((p : P) * σ p)) =
    (τ (ε (p : P)) * (h : B)) * τ (τ (ε (p : P)) * (h : B))
  calc
    (g : B) * ε (a * ((p : P) * σ p)) = (g : B) * (ε (σ p) * (ε a * ε p)) := by
      rw [← map_mul, ← map_mul]
      exact congrArg (fun x : P => (g : B) * ε x) (by ac_rfl)
    _ = ((g : B) * ε (σ p) * ↑g⁻¹) * ((g : B) * ε a) * ε p := by
      rw [mul_assoc ((g : B) * ε (σ p)) (↑g⁻¹ : B),
        ← mul_assoc (↑g⁻¹ : B) (g : B), Units.inv_mul, one_mul]
      simp only [mul_assoc]
    _ = _ := by
      rw [← hε, ha, τ.map_mul, τ.apply_apply]
      simp only [mul_assoc]

/-- The intertwining equation for the twist extends to every commutative
coefficient algebra. -/
theorem unitaryEmbeddingTwist_baseChange {F P B R : Type*} [Field F]
    [CommRing P] [Ring B] [CommRing R] [Algebra F P] [Algebra F B] [Algebra F R]
    (σ : FirstKindInvolution F P) (τ : FirstKindInvolution F B) (ε : P →ₐ[F] B)
    (g : Bˣ) (hε : ∀ x : P, τ (ε x) = (g : B) * ε (σ x) * ↑g⁻¹)
    (x : R ⊗[F] P) :
    τ.baseChange R (Algebra.TensorProduct.map (AlgHom.id R R) ε x) =
      ((1 : R) ⊗ₜ[F] (g : B)) *
        Algebra.TensorProduct.map (AlgHom.id R R) ε (σ.baseChange R x) *
        ((1 : R) ⊗ₜ[F] (↑g⁻¹ : B)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp [Algebra.TensorProduct.tmul_mul_tmul, hε]
  | add x y hx hy => simp [map_add, hx, hy, mul_add, add_mul]

end Langlands.CentralSimple
