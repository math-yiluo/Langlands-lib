/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage

/-! # Scalar extension of constant coefficient sheaves

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 094I
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- The ring underlying the constant commutative ring sheaf. Source: Stacks, Tag 094I
(auxiliary; not a blueprint node). -/
noncomputable abbrev constantCoefficientRing (B : Type u) [CommRing B] :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))

/-- The coefficient unit, with the commutative-ring structure forgotten. Source: Stacks,
Tag 094I (auxiliary; not a blueprint node). -/
noncomputable def constantCoefficientUnit (B : Type u) [CommRing B] :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ (constantCoefficientRing J B).obj :=
  Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat RingCat)

/-- Forgetting commutativity preserves local injectivity of the sheafification unit.
Source: Stacks, Tag 03DA
(auxiliary; not a blueprint node).
Proof: the underlying functions and equalizer sieves are unchanged by forgetting
commutativity; the sheafification unit is locally injective. -/
theorem constantCoefficientUnit_isLocallyInjective (B : Type u) [CommRing B] :
    Presheaf.IsLocallyInjective J (constantCoefficientUnit J B) := by
  constructor
  intro X x y h
  exact Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))) x y h

/-- Forgetting commutativity preserves local surjectivity of the sheafification unit.
Source: Stacks, Tag 03DA
(auxiliary; not a blueprint node).
Proof: the underlying functions and image sieves are unchanged by forgetting
commutativity; the sheafification unit is locally surjective. -/
theorem constantCoefficientUnit_isLocallySurjective (B : Type u) [CommRing B] :
    Presheaf.IsLocallySurjective J (constantCoefficientUnit J B) := by
  constructor
  intro X s
  exact Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))) s

attribute [instance] constantCoefficientUnit_isLocallyInjective
  constantCoefficientUnit_isLocallySurjective

/-- The existing constant-module presheaf, sheafified over the constant commutative
coefficient ring. Source: Stacks, Tag 094I
(auxiliary; not a blueprint node). -/
noncomputable def constantCoefficientModule (B : Type u) [CommRing B] :
    ModuleCat.{u} B ⥤ SheafOfModules.{u} (constantCoefficientRing J B) :=
  strictPerfectConstantPresheaf (C := C) B ⋙
    PresheafOfModules.sheafification (constantCoefficientUnit J B)

/-- Derived scalar extension, selected from the universal left-derived functor in
`derivedChangeOfRings`; its universal property determines it up to natural isomorphism.
Source: Stacks, Tag 06YY
(auxiliary; not a blueprint node). -/
noncomputable def constantCoefficientScalarExtension
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing J B))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing J D))] :
    DerivedCategory (SheafOfModules.{u} (constantCoefficientRing J B)) ⥤
      DerivedCategory (SheafOfModules.{u} (constantCoefficientRing J D)) :=
  (derivedChangeOfRings ((constantSheaf J CommRingCat.{u}).map
    (CommRingCat.ofHom f))).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

end SheafOfModules
