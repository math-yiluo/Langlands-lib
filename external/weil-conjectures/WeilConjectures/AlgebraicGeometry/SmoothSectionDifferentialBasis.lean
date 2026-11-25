/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.SmoothSectionDifferentialData
import WeilConjectures.RingTheory.SmoothConormalSequenceExact
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Stabilization of the differentials of a smooth section

Source: Stacks Project, More on Algebra, Tag 07M7, first paragraph.
(blueprint: lem-weil-pbc-smooth-section-differential-basis).
-/

@[expose] public section

universe u
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A smooth section admits, after an étale base extension and symmetric-algebra
stabilization, a finite basis of differentials represented by elements of its kernel.
This asserts no étaleness for the enlarged algebra or any quotient of it.

Source: Stacks Project, Tag 07M7, first paragraph and the choice of the `fᵢ` in the
second paragraph. (blueprint: lem-weil-pbc-smooth-section-differential-basis)

Proof:
1. The section is surjective since the structure map to `A/J` is surjective. Apply
   the smooth conormal sequence to identify its relative conormal module with
   `(A/J) ⊗[B] Ω[B/A]`. The image of `J/J²` is `(JB + N²)/N²`: for `b ∈ B`, lift
   `σ(b)` to `a ∈ A`, and for `x ∈ J` use `(b - a)x ∈ N²`.
2. The resulting module is finite projective, hence has a finite projective complement
   making its direct sum finite free. Lift this complement by Tag 07M5 over an étale
   algebra `A₁` with `A₁/JA₁ ≅ A/J`. Base change `B` and the section to `A₁`.
3. Tensor the base-changed algebra with the symmetric algebra of the lifted complement.
   The augmentation defines the extended section. Smoothness follows from Tag 07M6
   and stability under base change and composition. Its relative conormal module is
   the direct sum of the old conormal module and the reduced complement: the positive
   degree augmentation ideal modulo its square is the degree-one module. Reduction
   by the section kernel reduces this module to the lifted complement modulo `J`.
4. This sum is finite free. Choose a finite basis and lift its elements to the kernel.
   The conormal identification sends these lifts to the displayed differential basis.
   The map from `A₁` to `A/J` is the quotient followed by the quotient equivalence,
   hence is surjective. Retain the maps from `B` and to `A/J`; augmentation and base
   change give their required composite. -/
theorem exists_smooth_section_differential_basis
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (J : Ideal A) (σ : B →ₐ[A] A ⧸ J) :
    ∃ A₁ : CommAlgCat.{u} A,
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A A₁))) ∧
      ∃ (D : CommAlgCat.{u} A) (_ : Algebra A₁ D) (_ : IsScalarTower A A₁ D),
        Algebra.Smooth A₁ D ∧
        ∃ (j : B →ₐ[A] D) (τ : D →ₐ[A] A ⧸ J),
          τ.comp j = σ ∧
          Function.Surjective (τ.toRingHom.comp (algebraMap A₁ D)) ∧
          ∃ (n : ℕ) (f : Fin n → D), (∀ i, τ (f i) = 0) ∧
            letI : Algebra D (A ⧸ J) := τ.toRingHom.toAlgebra
            ∃ b : Module.Basis (Fin n) (A ⧸ J) ((A ⧸ J) ⊗[D] KaehlerDifferential A₁ D),
              ∀ i, b i = 1 ⊗ₜ[D] KaehlerDifferential.D A₁ D (f i) := by
  obtain ⟨A₁, hA₁, D, hAD, hTower, hD, j, τ, hτj, hsurj, hfree⟩ :=
    exists_smooth_section_differential_data A B J σ
  let : Algebra A₁ D := hAD
  let : IsScalarTower A A₁ D := hTower
  refine ⟨A₁, hA₁, D, hAD, hTower, hD, j, τ, hτj, hsurj, ?_⟩
  classical
  let : Algebra D (A ⧸ J) := τ.toRingHom.toAlgebra
  let η := τ.toRingHom.comp (algebraMap A₁ D)
  let : Algebra A₁ (A ⧸ J) := η.toAlgebra
  let : IsScalarTower A₁ D (A ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Smooth A₁ D := hD
  let : Module.Free (A ⧸ J) ((A ⧸ J) ⊗[D] KaehlerDifferential A₁ D) := hfree
  obtain ⟨hβ, u, hu, hinj, hex, hv⟩ :=
    Algebra.Extension.smooth_conormal_sequence_exact (A := A₁) (B := D)
      (C := A ⧸ J) hsurj
  let Q := Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom A₁ D (A ⧸ J)) hβ
  let M := (A ⧸ J) ⊗[D] KaehlerDifferential A₁ D
  let b := (Module.Free.chooseBasis (A ⧸ J) M).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex (A ⧸ J) M))
  have hlift : ∀ i, ∃ x : Q.ker, Q.cotangentComplex
      (Algebra.Extension.Cotangent.mk x) = b i := by
    intro i
    obtain ⟨y, hy⟩ := hv (b i)
    obtain ⟨x, hx⟩ := Algebra.Extension.Cotangent.mk_surjective y
    exact ⟨x, hx ▸ hy⟩
  choose f hf using hlift
  refine ⟨_, fun i ↦ (f i).1, ?_, b, ?_⟩
  · intro i
    exact (f i).2
  · intro i
    exact (hf i).symm

end AlgebraicGeometry
