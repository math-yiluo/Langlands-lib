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
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLiftProjectiveComplement
import WeilConjectures.AlgebraicGeometry.SymmetricStabilizationDifferentials
import WeilConjectures.RingTheory.SymmetricAlgebraSmooth
/-! # Free reduced differentials after stabilizing a smooth section

Source: Stacks Project, More on Algebra, Tag 07M7, first paragraph.
(blueprint: lem-weil-pbc-smooth-section-stabilization-free).
-/
@[expose] public section
universe u
namespace AlgebraicGeometry
open scoped TensorProduct
/-- A smooth section has free reduced differentials after étale base change and
symmetric-algebra stabilization. This does not choose a basis or any kernel lifts.

Source: Stacks Project, More on Algebra, Tag 07M7, first paragraph.
(blueprint: lem-weil-pbc-smooth-section-stabilization-free)

Proof:
1. Give `A/J` its `B`-algebra structure through the section. The reduced module
   `P = (A/J) ⊗[B] Ω[B/A]` is finite projective: smoothness makes the differential
   module finite projective and extension of scalars preserves these properties.
   Choose a finite projective complement `Kbar` with `P ⊕ Kbar` finite free.
2. Apply Tag 07M5 to `Kbar`. It gives an étale `A`-algebra `A₁`, a compatible
   quotient equivalence `α : A/J ≃ A₁/JA₁`, and a finite projective `A₁`-module `K`
   whose reduction corresponds to `Kbar`. Base change `B` to `B₁ = A₁ ⊗[A] B`.
   The map `a₁ ⊗ b ↦ class(a₁) * α(σ(b))` defines the base-changed section.
3. Put `D = B₁ ⊗[A₁] Sym[A₁](K)`. Both factors are smooth over `A₁`, hence so
   is `D`, by Tag 07M6 and base change and composition of smooth maps. The
   augmentation of the symmetric algebra gives `D → B₁`; compose with the
   base-changed section and `α⁻¹` to obtain `τ`. The canonical map `B → D`
   gives `j`, and augmentation on constants gives `τ.comp j = σ`.
4. Differentials of a tensor product split into the base changes of the two
   differential modules. The differential module of the symmetric algebra is
   its scalar extension of `K`, by the universal properties of derivations and
   the symmetric algebra: a derivation is uniquely determined by its restriction
   to the degree-one generators. Reducing this decomposition through `τ` gives
   `P ⊕ Kbar`, which is free by step 1. The map `A₁ → D → A/J` is the quotient
   map followed by `α⁻¹`, so it is surjective.

Edge cases: no nontriviality of the quotient is needed. If `J = ⊤`, all reduced
modules are zero and the quotient map still surjects; complements and all the
constructions above work over the zero ring. A rank-zero complement is allowed.
-/
theorem exists_smooth_section_differential_data
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (J : Ideal A) (σ : B →ₐ[A] A ⧸ J) :
    ∃ A₁ : CommAlgCat.{u} A,
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A A₁))) ∧
      ∃ (D : CommAlgCat.{u} A) (_ : Algebra A₁ D) (_ : IsScalarTower A A₁ D),
        Algebra.Smooth A₁ D ∧
        ∃ (j : B →ₐ[A] D) (τ : D →ₐ[A] A ⧸ J),
          τ.comp j = σ ∧
          Function.Surjective (τ.toRingHom.comp (algebraMap A₁ D)) ∧
          letI : Algebra D (A ⧸ J) := τ.toRingHom.toAlgebra
          Module.Free (A ⧸ J) ((A ⧸ J) ⊗[D] KaehlerDifferential A₁ D) := by
  classical
  let Q := A ⧸ J
  let : Algebra B Q := σ.toRingHom.toAlgebra
  let P := Q ⊗[B] KaehlerDifferential A B
  obtain ⟨A₁, hA₁, η, hη, K, hKAdd, hKModule, hKFin, hKProj, hfree⟩ :=
    exists_etale_lift_projective_complement A J P
  let : AddCommGroup K := hKAdd
  let : Module A₁ K := hKModule
  let : Module.Finite A₁ K := hKFin
  let : Module.Projective A₁ K := hKProj
  let S := SymmetricAlgebra A₁ K
  let : Algebra A S := ((algebraMap A₁ S).comp (algebraMap A A₁)).toAlgebra
  let : IsScalarTower A A₁ S := IsScalarTower.of_algebraMap_eq' rfl
  let D := S ⊗[A] B
  let ε : S →ₐ[A] A₁ :=
    (SymmetricAlgebra.algebraMapInv (R := A₁) (M := K)).restrictScalars A
  let τ : D →ₐ[A] Q := Algebra.TensorProduct.lift (η.comp ε) σ
    (fun _ _ ↦ Commute.all _ _)
  let j : B →ₐ[A] D := Algebra.TensorProduct.includeRight
  have hτj : τ.comp j = σ := by
    ext b
    change (η.comp ε) 1 * σ b = σ b
    rw [map_one, one_mul]
  have hτη : ∀ a : A₁, τ (algebraMap A₁ D a) = η a := by
    intro a
    change τ ((algebraMap A₁ S a) ⊗ₜ[A] (1 : B)) = η a
    change η (ε (algebraMap A₁ S a)) * σ 1 = η a
    rw [map_one, mul_one]
    congr 1
    exact (SymmetricAlgebra.algebraMapInv (R := A₁) (M := K)).commutes a
  let : Algebra.Smooth A₁ S := SymmetricAlgebra.smooth_of_finite_projective A₁ K
  let : Algebra.Smooth A₁ D := Algebra.Smooth.comp A₁ S D
  refine ⟨A₁, hA₁, CommAlgCat.of A D, inferInstance, inferInstance,
    inferInstance, j, τ, hτj, ?_, ?_⟩
  · intro q
    obtain ⟨a, ha⟩ := hη q
    exact ⟨a, (hτη a).trans ha⟩
  · let : Algebra A₁ Q := η.toRingHom.toAlgebra
    let : Algebra D Q := τ.toRingHom.toAlgebra
    let : Module.Free Q (P × (Q ⊗[A₁] K)) := hfree
    obtain ⟨e⟩ := symmetric_stabilization_differentials A B Q A₁ K σ η τ hτj hτη
    exact Module.Free.of_equiv e.symm


end AlgebraicGeometry
