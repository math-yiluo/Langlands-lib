/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheaves of modules form a Grothendieck abelian category

Let `R` be a sheaf of rings on a small site `(C, J)`. The category of sheaves of `R`-modules is
a Grothendieck abelian category:

* filtered colimits are exact, because the functor `SheafOfModules.toSheaf R` to sheaves of
  abelian groups preserves colimits and finite limits, reflects isomorphisms, and filtered
  colimits are exact in sheaves of abelian groups;
* the sheafifications of the free presheaves of modules on the representable presheaves form a
  small separating family, since the right adjoint of the sheafification is faithful.

## Main results

- `SheafOfModules.isSeparating_sheafification_freeYoneda`: the sheafified free modules on the
  representable presheaves form a separating family.
- `SheafOfModules.isGrothendieckAbelian`: `SheafOfModules.{u} R` is Grothendieck abelian.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafifications of the free presheaves of modules `R[yoneda X]` on the representable
presheaves form a separating family of sheaves of `R`-modules. -/
lemma isSeparating_sheafification_freeYoneda :
    ObjectProperty.IsSeparating (.ofObj fun X : C ↦ (PresheafOfModules.sheafification
      (𝟙 R.obj)).obj ((PresheafOfModules.free R.obj).obj (yoneda.obj X))) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  intro M N f g hfg
  refine (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
    (PresheafOfModules.freeYoneda.isSeparating R.obj _ _ ?_)
  rintro _ ⟨X⟩ a
  apply (adj.homEquiv _ _).symm.injective
  have h := hfg _ (ObjectProperty.ofObj_apply _ X) ((adj.homEquiv _ _).symm a)
  rw [← Adjunction.homEquiv_naturality_right_symm,
    ← Adjunction.homEquiv_naturality_right_symm] at h
  exact h

/-- **Sheaves of modules form a Grothendieck abelian category.** -/
theorem isGrothendieckAbelian : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  have : HasFilteredColimitsOfSize.{u, u} (SheafOfModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u, u} (SheafOfModules.{u} R) :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (toSheaf.{u} R)⟩
  have : HasSeparator (SheafOfModules.{u} R) :=
    ⟨_, (isSeparating_sheafification_freeYoneda R).isSeparator_coproduct⟩
  exact {}

end SheafOfModules

namespace SheafOfModules

universe v v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The category of sheaves of modules.** A sheaf of `R`-modules is a sheaf of abelian groups
with compatible `R(U)`-module structures on its sections, and a morphism is a morphism of the
underlying sheaves of abelian groups that is `R(U)`-linear on sections: the forgetful functor
`SheafOfModules.toSheaf R` to sheaves of abelian groups is faithful and additive. When
sheafification of abelian presheaves exists, `SheafOfModules R` is abelian
(`SheafOfModules.instAbelian`). (blueprint: `situation-conventions`) -/
theorem faithful_toSheaf_and_abelian :
    (toSheaf.{v} R).Faithful ∧ (toSheaf.{v} R).Additive ∧
      Nonempty (Abelian (SheafOfModules.{v} R)) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance⟩⟩

/-- **Colimits of sheaves of modules and the forgetful functor.** Let `R` be a sheaf of rings on
a site where abelian presheaves can be sheafified. Then: (1) the forgetful functor
`toSheaf R` to sheaves of abelian groups is faithful and exact; (2) sheaves of `R`-modules
have all small limits and colimits, a colimit being the sheafification of the colimit of the
underlying presheaves of modules; (3) `toSheaf R` preserves all small limits and colimits.
(blueprint: `situation-conventions`) -/
theorem toSheaf_exact_and_preservesLimitsColimits :
    (toSheaf.{v} R).Faithful ∧ PreservesFiniteLimits (toSheaf.{v} R) ∧
      PreservesFiniteColimits (toSheaf.{v} R) ∧
      HasLimitsOfSize.{v, v} (SheafOfModules.{v} R) ∧
      HasColimitsOfSize.{v, v} (SheafOfModules.{v} R) ∧
      PreservesLimitsOfSize.{v, v} (toSheaf.{v} R) ∧
      PreservesColimitsOfSize.{v, v} (toSheaf.{v} R) ∧
      ∀ {K : Type v} [SmallCategory K] (F : K ⥤ SheafOfModules.{v} R),
        Nonempty (colimit F ≅
          (PresheafOfModules.sheafification (𝟙 R.obj)).obj (colimit (F ⋙ forget R))) := by
  have : PreservesLimitsOfSize.{v, v} (toSheaf.{v} R ⋙ sheafToPresheaf J AddCommGrpCat.{v}) :=
    inferInstanceAs (PreservesLimitsOfSize (forget.{v} R ⋙ PresheafOfModules.toPresheaf R.obj))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf J AddCommGrpCat.{v}),
    ⟨fun {K} _ ↦ inferInstance⟩, fun {K} _ F ↦ ?_⟩
  let L := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  have : PreservesColimitsOfSize.{v, v} L := adj.leftAdjoint_preservesColimits
  let e : F ≅ (F ⋙ forget R) ⋙ L :=
    (F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F (asIso adj.counit).symm)
  exact ⟨HasColimit.isoOfNatIso e ≪≫ (preservesColimitIso L (F ⋙ forget R)).symm⟩


end SheafOfModules
