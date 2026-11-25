/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackMate

/-! # Affine extension and sections with independent localization universes
Source: Stacks Project, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: lem-sc-mixed-extension-sections-unit).
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

/-- On affine bases, extension of derived sections is sections of derived pullback,
with the comparison pinned by its adjunction unit. This statement involves only g
and a quasi-coherent object Q, with no f or base-change square.
Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW; Tag 0AA7,
construction of the canonical scalar-extension adjunct.
(blueprint: lem-sc-mixed-extension-sections-unit).

Proof:
1. Identify Y and Y' with spectra of their global rings using isoSpec. Transport Q
through the affine quasi-coherent derived equivalence. Its inverse is derived
sections with the global ring action. Take a K-flat resolution P of this module
complex; exact tilde identifies its localization with Q.
2. Tilde of P is K-flat. The natural tilde/pullback comparison identifies Lg*Q
with tilde of extension of P. The counit of the affine equivalence over Y' then
identifies its derived sections with extension of the derived sections of Q.
3. On these complexes, the tensor/sections adjunction has the same unit as the
sheaf pullback/direct-image adjunction. Localization preserves this equation.
Compare the resulting extension adjunction with mixedGlobalExtensionAdjunction
by uniqueness of left adjoints to the fixed derived scalar restriction, preserving
its unit. This gives a and the asserted unit equation.
4. On sheaves the sections/direct-image comparison is identity. Its right-derived
unit equation identifies the localized right comparison with
mixedGlobalSectionsDirectImageIso g, by right-derived uniqueness. All localizations
are carried out in their own universes, so w and wA need not be equal.
For Q=0, identity g, or the empty affine scheme the same comparison and unit equation
apply; no flatness, boundedness, or Tor-independence assertion is used. -/
theorem exists_mixedExtensionSectionsUnit
    {Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y'] (g : Y' ⟶ Y)
    (Q : schemeDerivedCategory Y) (hQ : schemeDerivedQCohProperty Y Q) :
    ∃ a : (mixedGlobalExtension g).obj ((schemeDerivedGlobalSections Y).obj Q) ≅
        (schemeDerivedGlobalSections Y').obj ((derivedPullback g).obj Q),
      (mixedGlobalExtensionAdjunction g).unit.app ((schemeDerivedGlobalSections Y).obj Q) ≫
          (schemeGlobalScalarRestriction g).map a.hom =
        (schemeDerivedGlobalSections Y).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
          (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q) := by
  obtain ⟨a, ha⟩ := exists_mixedAffineSectionsPullbackMate g Q hQ
  refine ⟨a, ?_⟩
  have h := ha ((derivedPullback g).obj Q) (𝟙 _)
  rw [(schemeHomPullbackAdjunction g).homEquiv_id] at h
  erw [(schemeDerivedGlobalSections Y').map_id, Category.comp_id] at h
  have h' := congrArg ((mixedGlobalExtensionAdjunction g).homEquiv _ _) h
  rw [Equiv.apply_symm_apply, (mixedGlobalExtensionAdjunction g).homEquiv_unit] at h'
  exact h'.symm

end AlgebraicGeometry
