/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits

/-! # The canonical scalar-forgetting inverse-image comparison

Source: Stacks Project, Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
namespace RawModuleScalarComparison









/-- The inverse of the canonical unit-compatible coefficient comparison. Source: Stacks
  Project, Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev pullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar (ModuleCat.{u + 1} Λ) f ⋙ moduleAbelianForget Λ X ≅
      moduleAbelianForget Λ Y ⋙ upperStar AddCommGrpCat.{u + 1} f :=
  (moduleAbelianUpperStarIso Λ f).symm

/-- The inverse comparison on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (pullbackIso Λ f).inv.app G

/-- The free abelian represented sheaf of an etale object.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev freeAbelian (S : Scheme.{u}) (U : S.Etale) :=
  (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)

/-- Send the represented abelian generator to the represented module generator.
Source: Stacks Project, Tag 03FD, the equality of section complexes.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable def freeMap (Λ : Type (u + 1)) [CommRing Λ]
    (S : Scheme.{u}) (U : S.Etale) :
    freeAbelian S U ⟶ (moduleAbelianForget Λ S).obj ((freeSheaf Λ S).obj U) := by
  let e : (freeAbelian S U ⟶ (moduleAbelianForget Λ S).obj ((freeSheaf Λ S).obj U)) ≃
      ((moduleAbelianForget Λ S).obj ((freeSheaf Λ S).obj U)).obj.obj (op U) :=
    ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) _).trans
      ((((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv)
  exact e.symm ((freeSheafHomEquiv Λ U ((freeSheaf Λ S).obj U)) (𝟙 _))

end RawModuleScalarComparison
end AlgebraicGeometry.Etale
