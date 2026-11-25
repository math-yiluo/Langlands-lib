/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The underlying sheaf of abelian groups of a sheaf of modules preserves colimits

Colimits of sheaves of modules are the sheafifications of the colimits of the underlying
presheaves of modules, and the sheafification of presheaves of modules commutes with forgetting
the module structure (`PresheafOfModules.sheafificationCompToSheaf`). Hence the functor
`SheafOfModules.toSheaf R` to sheaves of abelian groups preserves colimits.

## Main results

- `SheafOfModules.preservesColimitsOfShape_toSheaf`: `SheafOfModules.toSheaf R` preserves
  colimits of every shape for which presheaves of modules and of abelian groups have colimits.
- `SheafOfModules.preservesFiniteColimits_toSheaf`: in particular `SheafOfModules.toSheaf R`
  preserves finite colimits, so, together with `PreservesFiniteLimits`, it is exact.
- `PresheafOfModules.sheafificationHomEquiv_symm_comp`: the bijection of the universal property
  of the sheafification is natural in the target sheaf.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The functor `SheafOfModules.toSheaf R` to sheaves of abelian groups preserves colimits: a
diagram of sheaves of modules is the sheafification of its underlying diagram of presheaves of
modules, and sheafification followed by `toSheaf` is `toPresheaf` followed by the
sheafification of presheaves of abelian groups, which both preserve colimits. -/
instance preservesColimitsOfShape_toSheaf (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (toSheaf.{v} R) where
  preservesColimit {F} := by
    let L := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
    let G := F ⋙ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj))
    let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
    have : PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{v}) :=
      (sheafificationAdjunction J AddCommGrpCat.{v}).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimit G (L ⋙ toSheaf.{v} R) :=
      preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
    let hc := colimit.isColimit G
    have : PreservesColimit (G ⋙ L) (toSheaf.{v} R) :=
      preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
        (isColimitOfPreserves (L ⋙ toSheaf.{v} R) hc)
    exact preservesColimit_of_iso_diagram (toSheaf.{v} R) e

/-- `SheafOfModules.toSheaf R` preserves finite colimits. -/
instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) where
  preservesFiniteColimits _ := inferInstance

end SheafOfModules

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

lemma sheafificationHomEquiv_symm_comp {P : PresheafOfModules.{v} R₀}
    {F G : SheafOfModules.{v} R}
    (f : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) (g : F ⟶ G) :
    (sheafificationHomEquiv α).symm (f ≫ (restrictScalars α).map g.val) =
      (sheafificationHomEquiv α).symm f ≫ g := by
  obtain ⟨h, rfl⟩ := (sheafificationHomEquiv α).surjective f
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq]
  apply (toPresheaf R₀).map_injective
  rw [toPresheaf_map_sheafificationHomEquiv_def, Functor.map_comp,
    toPresheaf_map_sheafificationHomEquiv_def, SheafOfModules.comp_val, Category.assoc]
  rfl

end PresheafOfModules

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- **Universal property of the sheafification of a presheaf of modules.** Every morphism `f`
from a presheaf of modules `P` to (the restriction of scalars of) a sheaf of modules `F` factors
uniquely through the unit `P ⟶ P^#` of the sheafification adjunction
`PresheafOfModules.sheafificationAdjunction`: the sheafification functor is left adjoint to the
inclusion of sheaves of modules into presheaves of modules. On underlying abelian presheaves,
`P^#` is the sheafification of `P` (`PresheafOfModules.sheafificationCompToSheaf`).
(blueprint: `def-weil-presheaf-modules-sheafification`) -/
theorem existsUnique_sheafification_unit_comp (P : PresheafOfModules.{v} R₀)
    (F : SheafOfModules.{v} R)
    (f : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    ∃! g : (sheafification α).obj P ⟶ F,
      (sheafificationAdjunction α).unit.app P ≫
        (restrictScalars α).map ((SheafOfModules.forget _).map g) = f := by
  refine ⟨((sheafificationAdjunction α).homEquiv _ _).symm f, ?_, fun g hg ↦ ?_⟩
  · have := ((sheafificationAdjunction α).homEquiv _ _).apply_symm_apply f
    rwa [Adjunction.homEquiv_unit] at this
  · rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit]
    exact hg


end PresheafOfModules
