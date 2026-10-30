/-
The five proposition bodies in this file are adapted from the theorem statements in the files
`Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.lean`,
`Theorems/Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.lean`,
`Theorems/Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.lean`,
`Theorems/Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.lean` and
`Theorems/Thm_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`. The adaptation turns each theorem declaration into a `Prop`-valued definition
whose binders are universally quantified, renames it, moves it to the namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation`, replaces the imports by Mathlib imports and
omits the proof terms.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Descent of schemes and morphism properties to finitely generated subalgebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- A quasi-compact, quasi-separated morphism of finite presentation to `Spec A` is the base
change of such a morphism to `Spec T`, for a finitely generated `A₀`-subalgebra `T` of `A`
containing any given finite set. -/
def SchemeSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact g] [QuasiSeparated g]
    [LocallyOfFinitePresentation g] (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))

/-- Smoothness of the base change to `Spec A` of a quasi-compact morphism of finite
presentation to `Spec A₀` already holds after base change to `Spec T`, for a finitely
generated `A₀`-subalgebra `T` of `A` containing any given finite set. -/
def SmoothSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f]
    [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))

/-- Separatedness of the base change to `Spec A` of a quasi-compact, quasi-separated morphism
to `Spec A₀` already holds after base change to `Spec T`, for a finitely generated
`A₀`-subalgebra `T` of `A` containing any given finite set. -/
def IsSeparatedSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))]
    (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))

/-- Over a noetherian `A₀`, properness of the base change to `Spec A` of a separated,
quasi-compact morphism of finite type to `Spec A₀` already holds after base change to
`Spec T`, for a finitely generated `A₀`-subalgebra `T` of `A` containing any given finite
set. -/
def IsProperSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFiniteType f]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))

/-- Over a noetherian `A₀`, geometric connectedness of the fibres of the base change to
`Spec A` of a smooth proper morphism to `Spec A₀` already holds after base change to
`Spec T`, for a finitely generated `A₀`-subalgebra `T` of `A` containing any given finite
set. -/
def GeometricallyConnectedSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsProper f] [Smooth f]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))]
    (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      GeometricallyConnected
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))

end Langlands.AlgebraicGeometry.NoetherianApproximation
