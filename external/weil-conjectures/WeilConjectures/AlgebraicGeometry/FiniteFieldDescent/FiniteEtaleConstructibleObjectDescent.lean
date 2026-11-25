/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Finite-stage constructible descent component

Source: Stacks Project, Lemma 09YU (3).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- The canonical fibre product `Y_A` at a field extension `A/K`.
Source: Stacks Lemma 09YU (3) (blueprint: new-sfb-finite-etale-constructible-object-descent). -/
noncomputable abbrev scheme (A : Type u) [Field A] [Algebra K A] : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The canonical transition `Y_B ⟶ Y_A` induced by a `K`-algebra map `A ⟶ B`.
Source: Stacks Lemma 09YU (3) (blueprint: new-sfb-finite-etale-constructible-object-descent). -/
noncomputable def projection {A B : Type u} [Field A] [Field B] [Algebra K A]
    [Algebra K B] (h : A →ₐ[K] B) : scheme f B ⟶ scheme f A :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom h.toRingHom)) (𝟙 _)
    (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext x
      exact (h.commutes x).symm)

/-- The derived inverse-image functor along a transition of finite stages.
Source: Stacks Lemma 09YU (3) (blueprint: new-sfb-finite-etale-constructible-object-descent). -/
noncomputable abbrev pull (Λ : Type (u + 1)) [CommRing Λ]
    {A B : Type u} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (h : A →ₐ[K] B) :=
  (upperStar (ModuleCat.{u + 1} Λ) (projection f h)).leftDerivedFunctor

/-- The bounded constructible finite-Tor property at one finite stage.
Source: Stacks Lemma 09YU (3) (blueprint: new-sfb-finite-etale-constructible-object-descent). -/
abbrev ctf (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [Field A] [Algebra K A]
    (P : DerivedCategoryModule Λ (scheme f A)) : Prop :=
  DerivedCategory.boundedConstructibleFiniteTor Λ (scheme f A) P

/-- Object descent for bounded constructible finite-Tor complexes.
Source: Stacks Lemma 09YU (3), essential-surjectivity paragraph
(blueprint: new-sfb-finite-etale-constructible-object-descent).

Proof: finite intermediate fields of L/K form a directed system; Y_L is their affine
inverse limit and each transition is finite etale. All stages and Y_L are Noetherian,
since Y is finite type over a field. Replace P by a bounded complex of flat constructible
modules using the finite-Tor model theorem. Descend its finitely many nonzero terms
by constructible-module limit descent, then descend the finitely many differential
maps at a common larger finite stage using full faithfulness. Enlarge the stage again
so that the finitely many equations d composed with d = 0 hold. Faithfully flat
surjectivity of Y_L to this stage detects flatness on stalks; constructibility already
holds for the descended terms. The resulting bounded flat constructible complex has
bounded constructible cohomology and finite Tor amplitude. Its derived pullback is
represented by the original flat complex, giving the required isomorphism to P.
The zero complex, empty scheme and identity extension satisfy the same construction. -/
theorem finiteEtaleConstructibleObjectDescent
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [Algebra.IsSeparable K L] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : DerivedCategoryModule Λ (scheme f L)) (hP : ctf f Λ P) :
    ∃ (E : IntermediateField K L), FiniteDimensional K E ∧
      ∃ (P_E : DerivedCategoryModule Λ (scheme f E)), ctf f Λ P_E ∧
        Nonempty ((pull f Λ (IntermediateField.val E)).obj P_E ≅ P) := by
  sorry

end AlgebraicGeometry.Etale.FiniteFieldDescent
