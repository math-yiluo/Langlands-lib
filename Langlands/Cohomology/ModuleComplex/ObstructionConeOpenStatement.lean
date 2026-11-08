import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Field.Defs

/-! # Openness of first-cohomology vanishing for an obstruction cone: statement -/

universe u

open TensorProduct

namespace Langlands.Cohomology.ModuleComplex.ObstructionCone

/-- First cohomology of the obstruction cone vanishes with coefficients in `M`.

The data are a complex `(C, d)` of `A`-modules, an `A`-linear map `δ : Q → F`,
a degree-one cochain `θ ∈ C¹ ⊗ F` and a degree-two cochain `z ∈ C² ⊗ Q`.
The condition says: for every `c ∈ C¹ ⊗ M` and every `A`-linear `φ : Q → M`
with `d c + φ_* z = 0`, there are `b ∈ C⁰ ⊗ M` and an `A`-linear `D : F → M`
with `c = d b + D_* θ` and `φ + D ∘ δ = 0`. -/
def HOneVanishes {A : Type u} [CommRing A]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
    (d : ∀ i, C i →ₗ[A] C (i + 1))
    {F Q : Type u} [AddCommGroup F] [Module A F] [AddCommGroup Q] [Module A Q]
    (δ : Q →ₗ[A] F) (θ : C 1 ⊗[A] F) (z : C 2 ⊗[A] Q)
    (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (c : C 1 ⊗[A] M) (φ : Q →ₗ[A] M),
    (d 1).rTensor M c + φ.lTensor (C 2) z = 0 →
      ∃ (b : C 0 ⊗[A] M) (D : F →ₗ[A] M),
        c = (d 0).rTensor M b + D.lTensor (C 1) θ ∧ φ + D ∘ₗ δ = 0

/-- Openness of first-cohomology vanishing for an obstruction cone over a
noetherian ring. Let `(C, d)` be a bounded complex of flat `A`-modules with
finitely generated cohomology, `F` a finite projective module, `Q` a finite
module, `δ : Q → F`, `θ ∈ C¹ ⊗ F` and `z ∈ C² ⊗ Q` with `d θ = δ_* z` and
`d z = 0`. If `HOneVanishes` holds with coefficients in a field `k` over `A`,
then some `g ∈ A` with nonzero image in `k` has the following property: for
every `A`-algebra `S` in which `g` is a unit, `HOneVanishes` holds with
coefficients in every `S`-module. -/
def OpenStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
    [∀ i, Module.Flat A (C i)]
    (d : ∀ i, C i →ₗ[A] C (i + 1)), (∀ i, d (i + 1) ∘ₗ d i = 0) →
    ∀ (n : ℕ), (∀ i, n < i → Subsingleton (C i)) →
    Module.Finite A (LinearMap.ker (d 0)) →
    (∀ i, Module.Finite A (LinearMap.ker (d (i + 1)) ⧸
      (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) →
    ∀ (F Q : Type u) [AddCommGroup F] [Module A F] [Module.Finite A F]
      [Module.Projective A F] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
      (δ : Q →ₗ[A] F) (θ : C 1 ⊗[A] F) (z : C 2 ⊗[A] Q),
      (d 1).rTensor F θ = δ.lTensor (C 2) z →
      (d 2).rTensor Q z = 0 →
      ∀ (k : Type u) [Field k] [Algebra A k],
        HOneVanishes C d δ θ z k →
        ∃ g : A, algebraMap A k g ≠ 0 ∧
          ∀ (S : Type u) [CommRing S] [Algebra A S], IsUnit (algebraMap A S g) →
            ∀ (M : Type u) [AddCommGroup M] [Module S M] [Module A M]
              [IsScalarTower A S M], HOneVanishes C d δ θ z M

end Langlands.Cohomology.ModuleComplex.ObstructionCone
