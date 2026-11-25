/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
import WeilConjectures.AlgebraicGeometry.MixedSectionsCompositionKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Composition of normalized mixed Leray comparisons
Source: Stacks Project, cohomology.tex, Tags 08HY, 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-composition-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

-- Checking canonical comparison choices expands derived-functor and sheaf instances.
/-- Normalized mixed Leray comparisons compose with the normalized direct-image
comparison and restriction along a composite.
Source: Stacks Project, Tags 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-composition-coherence).

Proof: Let J be a K-injective representative on X. Precompose both sides with the
pasted right-derived unit for f_* followed by g_* followed by global sections on Z.
Use the unit equation of exists_derivedModuleDirectImageComposition and those of
exists_mixedGlobalSectionsDirectImageIso for f, g and f followed by g. Naturality
moves the units past the composition comparisons. Exact scalar restriction allows
its unit to move through localization. Both sides become the localization of the
identity map on sections over X: the underived Leray comparisons are identity on
elements, and restriction along the composite has the same scalar action as the
two successive restrictions. The mapDerivedCategoryCompIso in the scalar comparison
records precisely this equality after localization. Direct image and global sections
are acyclic on the required K-injective representatives, so the pasted unit is
invertible; cancel it. Transport the equality along a K-injective resolution to F.
Sheaf and module localization universes remain independent. For identities this is
the unit law, and zero objects and empty schemes require no additional assumption. -/
theorem mixedSections_composition_coherence
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : schemeDerivedCategory X) :
    let e : schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f ≫ g) :=
      schemeNormalizedDirectImageCompIso f g
    (mixedGlobalSectionsDirectImageIso g).hom.app ((schemeDerivedDirectImage f).obj F) ≫
        (schemeGlobalScalarRestriction g).map
          ((mixedGlobalSectionsDirectImageIso f).hom.app F) =
      (schemeDerivedGlobalSections Z).map (e.hom.app F) ≫
        (mixedGlobalSectionsDirectImageIso (f ≫ g)).hom.app F ≫
        (schemeGlobalScalarRestrictionCompIso f g).hom.app
          ((schemeDerivedGlobalSections X).obj F) := by
  let A := schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ⋙
    schemeDerivedGlobalSections Z
  let B := schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f ⋙
    schemeGlobalScalarRestriction g
  let α : A ⟶ B :=
    Functor.whiskerLeft (schemeDerivedDirectImage f) (mixedGlobalSectionsDirectImageIso g).hom ≫
      Functor.whiskerRight (mixedGlobalSectionsDirectImageIso f).hom
        (schemeGlobalScalarRestriction g)
  let β : A ⟶ B :=
    Functor.whiskerRight (schemeNormalizedDirectImageCompIso f g).hom
      (schemeDerivedGlobalSections Z) ≫
      (mixedGlobalSectionsDirectImageIso (f ≫ g)).hom ≫
      Functor.whiskerLeft (schemeDerivedGlobalSections X)
        (schemeGlobalScalarRestrictionCompIso f g).hom
  change α.app F = β.app F
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective F
  let e := eI ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
  apply (cancel_mono (B.map e.hom)).1
  rw [← α.naturality, ← β.naturality]
  congr 1
  exact mixedSections_composition_coherence_on_kInjective f g I

end AlgebraicGeometry
