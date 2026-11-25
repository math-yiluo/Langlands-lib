/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.AlgebraicGeometry.StrictTowerOperations

/-!
# Coefficient parameters and normalization formulas for locally closed extension

Source: Stacks Project, Tags 01OV, 01IO, 03D2 and 03D8.
(auxiliary; not a blueprint node).

These existing parameter definitions are moved verbatim from
`LocallyClosedModuleExtensionCoherence` and publicly reexported there.
The normalization predicates name the existing equations over abstract categories;
this lets the kernel compare their specializations without unfolding sheaf functors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A Noetherian scheme with an arbitrary commutative coefficient sheaf; a bundle of
parameters for the coherence assertion, not an additional hypothesis on coefficients.
Source: Stacks, Tags 01OV and 09A5
(auxiliary; not a blueprint node). -/
structure LocallyClosedCoefficients where
  scheme : Scheme.{u}
  locallyNoetherian : IsLocallyNoetherian scheme
  compact : CompactSpace scheme
  ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}

attribute [instance] LocallyClosedCoefficients.locallyNoetherian
  LocallyClosedCoefficients.compact

/-- A locally closed immersion with its inverse-image coefficient identification.
Taking the source ring literally to be inverse image is the special case `Iso.refl`;
allowing its identified presentation permits composition without silently equating rings.
Source: Stacks, Tags 01IO and 03D2
(auxiliary; not a blueprint node). -/
structure LocallyClosedCoefficientImmersion (S X : LocallyClosedCoefficients.{u}) where
  hom : S.scheme ⟶ X.scheme
  immersion : IsImmersion hom
  coefficient : (proEtaleSheafInverseImage hom CommRingCat.{u + 1}).obj X.ring ≅ S.ring

attribute [instance] LocallyClosedCoefficientImmersion.immersion

namespace LocallyClosedCoefficientImmersion

/-- Identity with the actual identity inverse-image comparison.
Source: Stacks, Tag 09A5 (auxiliary; not a blueprint node). -/
def identity (X : LocallyClosedCoefficients.{u}) : LocallyClosedCoefficientImmersion X X where
  hom := 𝟙 X.scheme
  immersion := inferInstance
  coefficient := (proEtaleRingInverseImageId X.scheme).app X.ring

/-- Composition with the actual composition of inverse-image coefficient identifications.
Source: Stacks, Tags 02V0 and 03D8
(auxiliary; not a blueprint node). -/
def comp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    LocallyClosedCoefficientImmersion T X where
  hom := b.hom ≫ a.hom
  immersion := inferInstance
  coefficient := proEtaleRingCompositeCoefficients b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient

/-- Exact inverse image with the specified inverse-image coefficients.
Source: Stacks, Tag 03D2 (auxiliary; not a blueprint node). -/
abbrev pull {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient

/-- Actual direct image with action through the coefficient adjunction unit.
Source: Stacks, Tag 03D3 (auxiliary; not a blueprint node). -/
abbrev push {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModuleDirectImage a.hom X.ring S.ring a.coefficient

end LocallyClosedCoefficientImmersion

/-- The specified open unit is inverse to restriction.
Source: Stacks, Tags 03DI and 09BN
(auxiliary; not a blueprint node). -/
def LocallyClosedOpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (adj : F ⊣ L) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    adj.unit.app M ≫ r.hom.app M = 𝟙 M

/-- Restriction agrees with the specified closed counit after comparison.
Source: Stacks, Tag 09AA
(auxiliary; not a blueprint node). -/
def LocallyClosedClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) (e : F ≅ P) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    r.hom.app M = L.map (e.hom.app M) ≫ d.app M

end AlgebraicGeometry.Scheme
