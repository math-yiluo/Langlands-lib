/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Flat coefficient restriction interface for module diagrams

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC; Modules on Sites,
Tag 03D3, specialized to compatible flat coefficient changes on diagram sites
(blueprint: def-weil-pbc-flat-ringed-diagram-input).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A choice of the induced module adjunction for an invertible structural ring map.
`AlgebraicInverseImage` is the small, single-universe presentation exported by the
recorded `AlgebraicInverseImageOfUniverses` module. The underlying Hom equation
specifies the ordinary module adjunction, including its unit and counit.
Source: Stacks 03D2--03D3
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
structure FlatRingedModuleImage
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (R : Sheaf K CommRingCat.{u}) (S : Sheaf H CommRingCat.{u}) where
  morphism : RingedToposMorphism
    ((sheafCompose H (forget₂ CommRingCat RingCat)).obj S)
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
  inverse : SheafOfModules.AlgebraicInverseImage morphism.inverse R S
  ringComparison : HEq inverse.ringUnderlying.hom morphism.ringMap
  additive : inverse.modules.Additive
  adjunction : inverse.modules ⊣ morphism.modules
  transpose : ∀ (M : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj S))
    (f : inverse.modules.obj M ⟶ N),
    (morphism.adj.homEquiv _ _)
      (inverse.moduleUnderlying.inv.app M ≫
        (SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).map f) =
      (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
        (adjunction.homEquiv M N f) ≫ morphism.underlying.hom.app N

attribute [instance] FlatRingedModuleImage.additive

/-- The coefficient square and the specified ordinary module images. The equality of
geometric adjunctions says that both coefficient systems use the same morphism of topoi;
`coherent` is exactly the commuting square of structural ring maps.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
structure FlatRingedDiagramInput
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (H : GrothendieckTopology D) where
  RV : Sheaf K CommRingCat.{u}
  SV : Sheaf K CommRingCat.{u}
  RU : Sheaf H CommRingCat.{u}
  SU : Sheaf H CommRingCat.{u}
  aV : RV ⟶ SV
  aU : RU ⟶ SU
  flatV : SheafOfModules.IsFlatOnSite.{u, u, u, u}
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map aV)).obj
        (SheafOfModules.unit.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj SV)))
  flatU : SheafOfModules.IsFlatOnSite.{u, u, u, u}
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).map aU)).obj
        (SheafOfModules.unit.{u} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj SU)))
  R : FlatRingedModuleImage RV RU
  S : FlatRingedModuleImage SV SU
  sameInverse : R.morphism.inverse = S.morphism.inverse
  sameDirect : R.morphism.direct = S.morphism.direct
  sameAdjunction : HEq R.morphism.adj S.morphism.adj
  coherent : R.inverse.ringUnderlying.hom ≫
      (sheafCompose H (forget CommRingCat)).map aU =
    R.morphism.inverse.map ((sheafCompose K (forget CommRingCat)).map aV) ≫
      eqToHom (congrArg (fun F ↦ F.obj
        ((sheafCompose K (forget CommRingCat)).obj SV)) sameInverse) ≫
      S.inverse.ringUnderlying.hom

namespace FlatRingedDiagramInput

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]

/-- The RU module diagram category, before localization.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev diagramsRU := J ⥤ ringedSiteModules.{u}
  ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.RU)

/-- The SU module diagram category, before localization.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev diagramsSU := J ⥤ ringedSiteModules.{u}
  ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU)

/-- The RV module diagram category, before localization.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev diagramsRV := J ⥤ ringedSiteModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.RV)

/-- The SV module diagram category, before localization.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev diagramsSV := J ⥤ ringedSiteModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.SV)

/-- The specified termwise R inverse image.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev inverseR : x.diagramsRV J ⥤ x.diagramsRU J :=
  (Functor.whiskeringRight J _ _).obj x.R.inverse.modules

/-- The specified termwise S inverse image.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev inverseS : x.diagramsSV J ⥤ x.diagramsSU J :=
  (Functor.whiskeringRight J _ _).obj x.S.inverse.modules

/-- The specified termwise R direct image.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev directR : x.diagramsRU J ⥤ x.diagramsRV J :=
  (Functor.whiskeringRight J _ _).obj x.R.morphism.modules

/-- The specified termwise S direct image.
Source: Stacks 03D3 (blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev directS : x.diagramsSU J ⥤ x.diagramsSV J :=
  (Functor.whiskeringRight J _ _).obj x.S.morphism.modules

/-- The derived RU-module diagram category.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev derivedRU (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    [HasDerivedCategory.{w} (x.diagramsRU J)] := DerivedCategory (x.diagramsRU J)

/-- The derived SU-module diagram category.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev derivedSU (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    [HasDerivedCategory.{w} (x.diagramsSU J)] := DerivedCategory (x.diagramsSU J)

/-- The derived RV-module diagram category.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev derivedRV (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    [HasDerivedCategory.{w} (x.diagramsRV J)] := DerivedCategory (x.diagramsRV J)

/-- The derived SV-module diagram category.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev derivedSV (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    [HasDerivedCategory.{w} (x.diagramsSV J)] := DerivedCategory (x.diagramsSV J)

/-- Integer-indexed cochain complexes of RU-module diagrams.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev cochainRU (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :=
    CochainComplex (x.diagramsRU J) ℤ

/-- Integer-indexed cochain complexes of SU-module diagrams.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev cochainSU (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :=
    CochainComplex (x.diagramsSU J) ℤ

/-- Integer-indexed cochain complexes of RV-module diagrams.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev cochainRV (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :=
    CochainComplex (x.diagramsRV J) ℤ

/-- Integer-indexed cochain complexes of SV-module diagrams.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev cochainSV (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :=
    CochainComplex (x.diagramsSV J) ℤ

/-- The specified R inverse image applied degreewise.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev inverseRComplex (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    cochainRV x J ⥤ cochainRU x J :=
    (x.inverseR J).mapHomologicalComplex (.up ℤ)

/-- The specified S inverse image applied degreewise.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev inverseSComplex (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    cochainSV x J ⥤ cochainSU x J :=
    (x.inverseS J).mapHomologicalComplex (.up ℤ)

/-- The specified R direct image applied degreewise.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev directRComplex (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    cochainRU x J ⥤ cochainRV x J :=
    (x.directR J).mapHomologicalComplex (.up ℤ)

/-- The specified S direct image applied degreewise.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev directSComplex (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    cochainSU x J ⥤ cochainSV x J :=
    (x.directS J).mapHomologicalComplex (.up ℤ)

/-- The actual restriction at U applied degreewise.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev restrictUComplex (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    cochainSU x J ⥤ cochainRU x J :=
    ((Functor.whiskeringRight J _ _).obj (SheafOfModules.restrictScalars.{u}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU))).mapHomologicalComplex (.up ℤ)

/-- The actual restriction at V applied degreewise.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-input). -/
abbrev restrictVComplex (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J] :
    cochainSV x J ⥤ cochainRV x J :=
    ((Functor.whiskeringRight J _ _).obj (SheafOfModules.restrictScalars.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV))).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} (x.diagramsRU J)]
  [HasDerivedCategory.{w} (x.diagramsSU J)]
  [HasDerivedCategory.{w} (x.diagramsRV J)]
  [HasDerivedCategory.{w} (x.diagramsSV J)]

end FlatRingedDiagramInput
end CategoryTheory
