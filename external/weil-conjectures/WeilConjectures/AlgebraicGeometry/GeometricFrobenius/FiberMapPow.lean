/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Powers of the geometric Galois Frobenius and base change

The base change `φ̄ = φ × 𝟙` of a morphism `φ` over a finite field `k` commutes with the powers
of the geometric Galois Frobenii.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)}

/-- The base change `φ̄` commutes with the powers of the geometric Galois Frobenii. -/
@[reassoc]
theorem geometricFiberMap_comp_geometricGaloisFrobenius_pow (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)
    (m : ℕ) :
    geometricFiberMap φ h ≫ (g.geometricGaloisFrobenius ^ m).asIso.hom =
      (f.geometricGaloisFrobenius ^ m).asIso.hom ≫ geometricFiberMap φ h := by
  induction m with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m ih =>
    rw [pow_succ, pow_succ, Aut.mul_asIso, Aut.mul_asIso, Iso.trans_hom, Iso.trans_hom,
      geometricFiberMap_comp_geometricGaloisFrobenius_assoc, ih, Category.assoc]

end AlgebraicGeometry.Scheme.Hom
