/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage

/-! # Locally constant finite type modules on a small site

Source: Stacks Project, Modules on Sites, Definition 093Q;
Cohomology on Sites, Tag 094H
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- The constant commutative-ring sheafification unit remains locally injective after
forgetting to rings. Source: Stacks, sheafification, Tags 00W1 and 094H
(auxiliary; not a blueprint node).
Proof: equality after the unit is locally equality before it by sheafification; forgetting
commutativity changes neither sections nor their equality. -/
theorem constantCommRingUnit_locallyInjective
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight
        (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u} RingCat.{u})) := by
  constructor
  intro X x y h
  exact Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))) x y h

attribute [instance] constantCommRingUnit_locallyInjective

/-- The constant commutative-ring sheafification unit remains locally surjective after
forgetting to rings. Source: Stacks, sheafification, Tags 00W1 and 094H
(auxiliary; not a blueprint node).
Proof: sections of a sheafification locally come from presheaf sections, and forgetting
commutativity leaves those same sections and local lifts. -/
theorem constantCommRingUnit_locallySurjective
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight
        (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
        (forget₂ CommRingCat.{u} RingCat.{u})) := by
  constructor
  intro U s
  exact Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))) s

attribute [instance] constantCommRingUnit_locallySurjective

/-- A module over the constant coefficient ring is locally constant of finite type if,
over every object, a covering sieve trivializes it with finitely generated constant values.
The constant module is the sheafification of the existing constant module presheaf along
the constant-ring sheafification unit. Restriction to the slice is `overFunctor`.

Source: Stacks Project, Modules on Sites, Definition 093Q;
Cohomology on Sites, Tag 094H
(auxiliary; not a blueprint node). -/
noncomputable def IsLocallyConstantFiniteType
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    (F : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ M : ModuleCat.{u} B, Module.Finite B M ∧
        Nonempty ((SheafOfModules.overFunctor _ U).obj F ≅
          (SheafOfModules.overFunctor _ U).obj
            ((PresheafOfModules.sheafification
              (Functor.whiskerRight
                (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
                (forget₂ CommRingCat.{u} RingCat.{u}))).obj
                  ((strictPerfectConstantPresheaf (C := C) B).obj M)))

end SheafOfModules
