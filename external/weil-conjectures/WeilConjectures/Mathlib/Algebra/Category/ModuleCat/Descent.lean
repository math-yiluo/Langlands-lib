/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Extension of scalars along a finite projective ring map preserves limits

For a finite projective `R`-module `P`, tensoring with `P` is isomorphic to `Hom(P^∨, -)`, a
right adjoint, so it preserves limits. Consequently extension of scalars along a ring map
`f : R →+* S` making `S` finite projective over `R` preserves limits. This is what makes the
transition functors `𝒪_E ⟶ 𝒪_{E'}` between `ℓ`-adic coefficient stages commute with direct
images of sheaves without sheafification.

## Main results

- `ModuleCat.tensorLeftIsoIhomDual`: `P ⊗ - ≅ Hom(P^∨, -)` for finite projective `P`.
- `ModuleCat.preservesLimits_extendScalars_of_finite_projective`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

open scoped TensorProduct

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- For a finite projective `R`-module `P`, `P ⊗ N ≃ Hom(P^∨, N)`, through the double dual. -/
noncomputable def tensorEquivHomDual (N : Type u) [AddCommGroup N] [Module R N] :
    P ⊗[R] N ≃ₗ[R] (Module.Dual R P →ₗ[R] N) :=
  (TensorProduct.congr (Module.evalEquiv R P) (LinearEquiv.refl R N)).trans
    (dualTensorHomEquiv R (Module.Dual R P) N)

lemma tensorEquivHomDual_tmul (N : Type u) [AddCommGroup N] [Module R N] (p : P) (n : N)
    (f : Module.Dual R P) : tensorEquivHomDual P N (p ⊗ₜ n) f = f p • n := by
  simp [tensorEquivHomDual]

/-- For a finite projective `R`-module `P`, `P ⊗ - ≅ Hom(P^∨, -)`. -/
noncomputable def tensorLeftIsoIhomDual :
    tensorLeft (ModuleCat.of R P) ≅ ihom (ModuleCat.of R (Module.Dual R P)) :=
  NatIso.ofComponents (fun N ↦ ((tensorEquivHomDual (R := R) P N).trans
    (ModuleCat.homLinearEquiv (R := R) (S := R)
      (M := ModuleCat.of R (Module.Dual R P)) (N := N)).symm).toModuleIso) (by
    intro N N' g
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p n
    apply ModuleCat.hom_ext
    ext f
    change (tensorEquivHomDual (R := R) P N' (p ⊗ₜ g n)) f =
      g ((tensorEquivHomDual (R := R) P N (p ⊗ₜ n)) f)
    simp [tensorEquivHomDual_tmul])

/-- Tensoring with a finite projective module preserves limits. -/
instance preservesLimits_tensorLeft_of_finite_projective :
    PreservesLimits (tensorLeft (ModuleCat.of R P)) :=
  preservesLimits_of_natIso (tensorLeftIsoIhomDual P).symm

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Extension of scalars along a ring map making `S` a finite projective `R`-module preserves
limits: composed with the conservative restriction of scalars it is tensoring with `S`. -/
lemma preservesLimits_extendScalars_of_finite_projective
    (h₁ : letI := f.toAlgebra; Module.Finite R S)
    (h₂ : letI := f.toAlgebra; Module.Projective R S) :
    PreservesLimits (ModuleCat.extendScalars.{_, _, u} f) := by
  let := f.toAlgebra
  have : PreservesLimits
      (ModuleCat.extendScalars.{_, _, u} f ⋙ ModuleCat.restrictScalars.{_, _, u} f) :=
    inferInstanceAs (PreservesLimits (tensorLeft (ModuleCat.of R S)))
  have : (ModuleCat.restrictScalars.{_, _, u} f).ReflectsIsomorphisms := by
    constructor
    intro A B g hg
    have h : IsIso ((forget (ModuleCat R)).map ((ModuleCat.restrictScalars f).map g)) :=
      inferInstance
    have : IsIso ((forget (ModuleCat S)).map g) := h
    exact isIso_of_reflects_iso g (forget (ModuleCat S))
  have := reflectsLimits_of_reflectsIsomorphisms (G := ModuleCat.restrictScalars.{_, _, u} f)
  exact preservesLimits_of_reflects_of_preserves _ (ModuleCat.restrictScalars f)

end ModuleCat
