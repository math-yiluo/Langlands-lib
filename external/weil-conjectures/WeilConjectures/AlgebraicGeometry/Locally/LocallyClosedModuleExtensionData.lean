/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionData

/-!
# Coefficient parameters and normalization formulas for locally closed extension

These existing parameter definitions are moved verbatim from
`LocallyClosedModuleExtensionCoherence` and publicly reexported there.
The normalization predicates name the existing equations over abstract categories;
this lets the kernel compare their specializations without unfolding sheaf functors.

## References

* Stacks Project, Tags 01OV, 01IO, 03D2 and 03D8
* Stacks, Tags 02V0 and 09AH
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


attribute [instance] LocallyClosedCoefficients.locallyNoetherian
  LocallyClosedCoefficients.compact


attribute [instance] LocallyClosedCoefficientImmersion.immersion

namespace LocallyClosedCoefficientImmersion





/-- The canonical inverse-image composition, fixed by the sectionwise fibre-product map. -/
def pullComp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    (a.comp b).pull ≅ a.pull ⋙ b.pull :=
  exchangeModuleComposition b.hom a.hom X.ring S.ring T.ring a.coefficient b.coefficient

end LocallyClosedCoefficientImmersion



/-- The composite of the two restriction comparisons and inverse-image composition. -/
def LocallyClosedCompositeRestrictionMap
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) (M : A) :
    Lab.obj (Ea.obj (Eb.obj M)) ⟶ M :=
  c.hom.app (Ea.obj (Eb.obj M)) ≫ Lb.map (ra.hom.app (Eb.obj M)) ≫ rb.hom.app M

/-- An objectwise comparison has a specified restriction. -/
def LocallyClosedObjectNormalization
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (L : D ⥤ C)
    (r : H ⋙ L ≅ 𝟭 C) {A : D} {M : C} (t : L.obj A ⟶ M) (e : A ≅ H.obj M) : Prop :=
  dsimp% only [Functor.comp_obj, Functor.id_obj]
    L.map e.hom ≫ r.hom.app M = t

/-- A natural binary comparison has the composite restriction normalization. -/
def LocallyClosedBinaryNormalization
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (H : A ⥤ C) (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (rh : H ⋙ Lab ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) (e : Eb ⋙ Ea ≅ H) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    Lab.map (e.hom.app M) ≫ rh.hom.app M =
      LocallyClosedCompositeRestrictionMap Ea Eb La Lb Lab ra rb c M

end AlgebraicGeometry.Scheme
