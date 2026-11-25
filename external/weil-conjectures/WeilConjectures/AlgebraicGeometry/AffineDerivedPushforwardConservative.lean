/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Affine derived direct image reflects isomorphisms

Source: Stacks Project, Derived Categories of Schemes, Tag 08I8,
Lemma 36.5.2 (blueprint: lem-sc-affine-derived-pushforward-conservative).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For an affine morphism of schemes, derived direct image reflects isomorphisms
between objects with quasi-coherent cohomology.
Source: Stacks Project, Tag 08I8, Lemma 36.5.2
(blueprint: lem-sc-affine-derived-pushforward-conservative).

Proof:
1. By `lem-sc-finite-affine-derived-equivalence` (Stacks, Tag 0AVW), affine direct
   image gives an equivalence from `D_QCoh(𝒪_X)` to `D_QCoh(f_*𝒪_X)` whose composite
   with restriction of scalars is `Rf_*`. Restriction of scalars reflects isomorphisms:
   the cone of a morphism of `f_*𝒪_X`-complexes is acyclic exactly when its underlying
   `𝒪_Y`-complex is acyclic, since restriction does not change cohomology groups.
   Thus invertibility of `Rf_*u` implies invertibility of the image of `u` under
   this equivalence.
2. An equivalence reflects isomorphisms: apply its quasi-inverse to the inverse
   obtained in step 1 and use the unit and counit isomorphisms to obtain an inverse
   to `u`. Consequently `u` is an isomorphism. -/
theorem schemeDerivedDirectImage_isIso_of_affine
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f]
    {E F : schemeDerivedCategory X}
    (hE : schemeDerivedQCohProperty X E) (hF : schemeDerivedQCohProperty X F)
    (u : E ⟶ F) [IsIso ((schemeDerivedDirectImage f).map u)] : IsIso u := by
  -- Scalar restriction leaves the underlying sheaf of abelian groups unchanged.
  let A := moduleRings (directImageAlgebraSpace f)
  let R := moduleRings Y.toRingedSpace
  let α : R ⟶ A := ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  let T := SheafOfModules.restrictScalars.{u} α
  have he : T ⋙ SheafOfModules.toSheaf.{u} R ≅ SheafOfModules.toSheaf.{u} A := Iso.refl _
  have : T.ReflectsIsomorphisms := by
    have : (T ⋙ SheafOfModules.toSheaf.{u} R).ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_iso he.symm
    exact reflectsIsomorphisms_of_comp T (SheafOfModules.toSheaf.{u} R)
  have : Limits.PreservesFiniteLimits T := by
    have : Limits.PreservesFiniteLimits
        (T ⋙ SheafOfModules.toSheaf.{u} R) :=
      Limits.preservesFiniteLimits_of_natIso he.symm
    exact Limits.preservesFiniteLimits_of_reflects_of_preserves
      T (SheafOfModules.toSheaf.{u} R)
  have : Limits.ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    { reflects := fun _ ↦
        Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : Limits.PreservesFiniteColimits T := by
    have : Limits.PreservesFiniteColimits
        (T ⋙ SheafOfModules.toSheaf.{u} R) :=
      Limits.preservesFiniteColimits_of_natIso he.symm
    exact Limits.preservesFiniteColimits_of_reflects_of_preserves
      T (SheafOfModules.toSheaf.{u} R)
  -- Choose a derived category for the auxiliary direct-image algebra only.
  let : HasDerivedCategory (SheafOfModules.{u} A) := HasDerivedCategory.standard _
  -- Exactness identifies derived cohomology with restricted cohomology.
  have : T.rightDerivedFunctor.ReflectsIsomorphisms := by
    constructor
    intro K L a ha
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ T).map a) :=
      (NatIso.isIso_map_iff (T.rightDerivedFunctorHomologyFunctorIso n) a).mpr
        (by dsimp; infer_instance)
    have : IsIso (T.map ((DerivedCategory.homologyFunctor _ n).map a)) := ‹_›
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map a) T
  -- Transport invertibility through the two comparisons and the equivalence.
  obtain ⟨Φ, _, S, ⟨eS⟩, ⟨eΦ⟩⟩ := finite_affine_derived_equivalence f
  let a : (⟨E, hE⟩ : schemeDerivedQCohCategory X) ⟶ ⟨F, hF⟩ :=
    (schemeDerivedQCohProperty X).homMk u
  have ha : IsIso (((schemeDerivedQCohProperty X).ι ⋙
      schemeDerivedDirectImage f).map a) := ‹_›
  have : IsIso ((Φ.functor ⋙ S ⋙ (schemeDerivedQCohProperty Y).ι).map a) :=
    (NatIso.isIso_map_iff eΦ a).mpr ha
  have : IsIso ((S ⋙ (schemeDerivedQCohProperty Y).ι).map (Φ.functor.map a)) := ‹_›
  have : IsIso (((directImageAlgebraDerivedQCohProperty f).ι ⋙
      T.rightDerivedFunctor).map (Φ.functor.map a)) :=
    (NatIso.isIso_map_iff eS (Φ.functor.map a)).mp ‹_›
  have : IsIso (T.rightDerivedFunctor.map
      ((directImageAlgebraDerivedQCohProperty f).ι.map (Φ.functor.map a))) := ‹_›
  have : IsIso ((directImageAlgebraDerivedQCohProperty f).ι.map (Φ.functor.map a)) :=
    isIso_of_reflects_iso _ T.rightDerivedFunctor
  have : IsIso (Φ.functor.map a) :=
    isIso_of_reflects_iso _ (directImageAlgebraDerivedQCohProperty f).ι
  have : IsIso a := isIso_of_reflects_iso _ Φ.functor
  exact (schemeDerivedQCohProperty X).ι.map_isIso a

end AlgebraicGeometry
