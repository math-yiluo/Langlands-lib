/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel

/-! # Exterior multiplication for splitting the first Koszul generator

Source: Stacks Project, More on Algebra, Tag 0664,
lemma-join-sequences-koszul-complex.
(blueprint: def-weil-pbc-koszul-join-graded).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

/-- Inclusion of the first generator.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
def koszulHeadInclusion (r : ℕ) : (Fin 1 →₀ A) →ₗ[A] Fin (r + 1) →₀ A :=
  Finsupp.lmapDomain A A (fun _ ↦ 0)

/-- Inclusion of the remaining generators.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
def koszulTailInclusion (r : ℕ) : (Fin r →₀ A) →ₗ[A] Fin (r + 1) →₀ A :=
  Finsupp.lmapDomain A A Fin.succ

/-- Multiplication of two homogeneous exterior elements.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
def koszulExteriorMul (s n k : ℕ) :
    (⋀[A]^n (Fin s →₀ A) ⊗[A] ⋀[A]^k (Fin s →₀ A)) →ₗ[A]
      ⋀[A]^(n + k) (Fin s →₀ A) :=
  TensorProduct.lift (LinearMap.mk₂ A
    (fun (x : ⋀[A]^n (Fin s →₀ A)) (y : ⋀[A]^k (Fin s →₀ A)) ↦
      (⟨x.val * y.val, by
        change _ ∈ (LinearMap.range (ExteriorAlgebra.ι A)) ^ (n + k)
        rw [pow_add]
        exact Submodule.mul_mem_mul x.property y.property⟩ :
          ⋀[A]^(n + k) (Fin s →₀ A)))
    (by intro x y z; apply Subtype.ext; exact add_mul _ _ _)
    (by intro c x y; apply Subtype.ext; exact smul_mul_assoc _ _ _)
    (by intro x y z; apply Subtype.ext; exact mul_add _ _ _)
    (by intro c x y; apply Subtype.ext; exact mul_smul_comm _ _ _))

/-- Wedge multiplication after the head and tail inclusions, in fixed exterior degrees.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
@[irreducible] def koszulJoinWedge (r n k : ℕ) :
    (⋀[A]^n (Fin 1 →₀ A) ⊗[A] ⋀[A]^k (Fin r →₀ A)) →ₗ[A]
      ⋀[A]^(n + k) (Fin (r + 1) →₀ A) :=
  (koszulExteriorMul (r + 1) n k).comp
    (TensorProduct.map (exteriorPower.map n (koszulHeadInclusion r))
      (exteriorPower.map k (koszulTailInclusion r)))

/-- The multiplication formula on a pure tensor.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
theorem koszulJoinWedge_tmul_coe (r n k : ℕ)
    (x : ⋀[A]^n (Fin 1 →₀ A)) (y : ⋀[A]^k (Fin r →₀ A)) :
    (koszulJoinWedge r n k (x ⊗ₜ[A] y) : ExteriorAlgebra A (Fin (r + 1) →₀ A)) =
      (exteriorPower.map n (koszulHeadInclusion r) x).val *
        (exteriorPower.map k (koszulTailInclusion r) y).val := by
  unfold koszulJoinWedge
  rfl

/-- The reindexing isomorphism in a nonpositive degree.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
def koszulGradedTermIso (r : ℕ) (a : Fin r → A) (m : ℕ) (i : ℤ) (hi : i ≤ 0) :
    (completedKoszulPower (A := A) r a m).X i ≅
      ModuleCat.of A (⋀[A]^((-i).toNat) (Fin r →₀ A)) :=
  (ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 1))).extendXIso
    ComplexShape.embeddingDownNat (by change -(((-i).toNat : ℕ) : ℤ) = i; omega)

/-- Multiplication on one summand of the total tensor, with zero in positive degrees.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
def koszulJoinSummand (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ)
    (p q i : ℤ) (h : p + q = i) :
    (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m).X p ⊗
        (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m).X q ⟶
      (completedKoszulPower (A := A) (r + 1) a m).X i :=
  if hp : p ≤ 0 then
    if hq : q ≤ 0 then
      ((koszulGradedTermIso 1 (fun _ ↦ a 0) m p hp).hom ⊗ₘ
        (koszulGradedTermIso r (fun j ↦ a j.succ) m q hq).hom) ≫
        ModuleCat.ofHom (koszulJoinWedge r (-p).toNat (-q).toNat) ≫
        ((ExteriorAlgebra.koszulComplex A (r + 1) (fun j ↦ a j ^ (m + 1))).extendXIso
          ComplexShape.embeddingDownNat
          (by change -(((-p).toNat + (-q).toNat : ℕ) : ℤ) = i; omega)).inv
    else 0
  else 0

/-- Exterior multiplication from the degreewise coproduct defining the total tensor.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
def koszulJoinGraded (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (i : ℤ) :
    (HomologicalComplex.tensorObj
      (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
      (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m)).X i ⟶
        (completedKoszulPower (A := A) (r + 1) a m).X i :=
  HomologicalComplex.mapBifunctorDesc (fun p q h ↦ koszulJoinSummand r a m p q i h)

end AlgebraicGeometry.Scheme
