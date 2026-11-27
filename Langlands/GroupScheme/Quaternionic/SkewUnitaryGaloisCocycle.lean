import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisDescent
import Langlands.Algebra.GaloisUnitHilbert90

/-! # Galois cocycles of matrices over `L ⊗ D`

Automorphisms of a field `L` over `F` act entrywise on matrices over `L ⊗[F] D`. A crossed
homomorphism `c` satisfies `c (s t) = c s · s(c t)`. Over an infinite base field every crossed
homomorphism of units is a coboundary `c s = p · s(p)⁻¹` (Hilbert 90).
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] {n : ℕ}
  {L : Type u} [Field L] [Algebra F L]

/-- The crossed homomorphism identity for the entrywise Galois action. -/
def IsCrossed (c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) : Prop :=
  ∀ s t, c (s * t) = c s * unitMap s.toAlgHom (c t)

theorem IsCrossed.map_one {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ}
    (hc : IsCrossed c) : c 1 = 1 := by
  have h := hc 1 1
  rw [mul_one] at h
  have h1 : unitMap (1 : L ≃ₐ[F] L).toAlgHom (c 1) = c 1 := by
    apply Units.ext
    exact coeffMap_id _
  rw [h1] at h
  exact (mul_eq_left.mp h.symm)

/-- The entrywise action of an automorphism as a ring automorphism of the matrix algebra. -/
def coeffAut (s : L ≃ₐ[F] L) : RingAut (Matrix (Fin n) (Fin n) (L ⊗[F] D)) :=
  RingEquiv.mapMatrix (Algebra.TensorProduct.congr s (AlgEquiv.refl : D ≃ₐ[F] D)).toRingEquiv

theorem coeffAut_apply (s : L ≃ₐ[F] L) (M : Matrix (Fin n) (Fin n) (L ⊗[F] D)) :
    coeffAut s M = coeffMap s.toAlgHom M := by
  ext i j
  rfl

/-- The entrywise action as a homomorphism to ring automorphisms. -/
def coeffAutHom : (L ≃ₐ[F] L) →* RingAut (Matrix (Fin n) (Fin n) (L ⊗[F] D)) where
  toFun := coeffAut
  map_one' := by
    ext M i j
    change coeffMap (1 : L ≃ₐ[F] L).toAlgHom M i j = M i j
    exact congrFun (congrFun (coeffMap_id M) i) j
  map_mul' s t := by
    ext M i j
    rw [RingAut.mul_apply, coeffAut_apply, coeffAut_apply, coeffAut_apply, coeffMap_comp]
    rfl

theorem tensorMap_smul (s : L ≃ₐ[F] L) (a : L) (x : L ⊗[F] D) :
    Algebra.TensorProduct.map s.toAlgHom (AlgHom.id F D) (a • x) =
      s a • Algebra.TensorProduct.map s.toAlgHom (AlgHom.id F D) x := by
  induction x using TensorProduct.inductionOn with
  | tmul l d =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
    rfl
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable [Infinite F] [FiniteDimensional F D] [FiniteDimensional F L]

/-- Hilbert 90 for crossed homomorphisms of units of matrices over `L ⊗ D`. -/
theorem IsCrossed.exists_coboundary {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ}
    (hc : IsCrossed c) :
    ∃ p : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ, ∀ s, c s = p * (unitMap s.toAlgHom p)⁻¹ := by
  let H : Subgroup (L ≃ₐ[F] L) := ⊤
  let α : H →* RingAut (Matrix (Fin n) (Fin n) (L ⊗[F] D)) := coeffAutHom.comp H.subtype
  have hα : ∀ (σ : H) (a : L) (v : Matrix (Fin n) (Fin n) (L ⊗[F] D)),
      α σ (a • v) = σ.val a • α σ v := by
    intro σ a v
    change coeffAut σ.val (a • v) = σ.val a • coeffAut σ.val v
    rw [coeffAut_apply, coeffAut_apply]
    ext i j
    exact tensorMap_smul σ.val a (v i j)
  obtain ⟨b, hb⟩ := Langlands.Algebra.exists_unit_coboundary (k := F) H α hα
    (fun σ => c σ.val) hc.map_one (fun σ τ => by
      change c (σ.val * τ.val) = _
      rw [hc σ.val τ.val]
      congr 1)
  refine ⟨b, fun s => ?_⟩
  have h := hb ⟨s, Subgroup.mem_top s⟩
  have he : Units.map (α ⟨s, Subgroup.mem_top s⟩).toMonoidHom b = unitMap s.toAlgHom b := by
    apply Units.ext
    change coeffAut s (b : Matrix (Fin n) (Fin n) (L ⊗[F] D)) =
      coeffMap s.toAlgHom (b : Matrix (Fin n) (Fin n) (L ⊗[F] D))
    rw [coeffAut_apply]
  rw [he] at h
  exact eq_mul_inv_of_mul_eq h

end Langlands.GroupScheme.Quaternionic.SkewUnitary
