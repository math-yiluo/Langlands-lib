/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence

/-! # The direct-image algebra and its quasi-coherent derived category

Source: Stacks Project, Derived Categories of Schemes, Tag 0AVW
(blueprint: def-sc-direct-image-algebra-derived-category).

## Main definitions

* `directImageAlgebraSpace` is the ringed space `(Y, f_* O_X)`.
* `toDirectImageAlgebraSpace` is its canonical morphism from `(X, O_X)`.
* `directImageAlgebraDerivedQCohProperty` and `directImageAlgebraDerivedQCohCategory`
  specify quasi-coherent cohomology over the direct-image algebra.
-/

@[expose] public section

universe u w

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The space `Y` with ring sheaf `f_* O_X`.
Source: Stacks, Tag 0AVW (blueprint: def-sc-direct-image-algebra-derived-category). -/
def directImageAlgebraSpace (f : X ⟶ Y) : RingedSpace.{u} where
  carrier := Y.toTopCat
  presheaf := ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf).obj
  IsSheaf := ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf).property

/-- The morphism `g : (X, O_X) → (Y, f_* O_X)` with identity map on the pushed-forward
ring sheaf. Source: Stacks, Tag 0AVW
(blueprint: def-sc-direct-image-algebra-derived-category). -/
def toDirectImageAlgebraSpace (f : X ⟶ Y) :
    X.toRingedSpace ⟶ directImageAlgebraSpace f :=
  ⟨{ base := f.base, c := 𝟙 _ }⟩

/-- A derived direct-image-algebra module has quasi-coherent cohomology over that algebra
in every integer degree, using the same `IsQuasicoherent` as the affine module correspondence.
Source: Stacks, Tag 0AVW (blueprint: def-sc-direct-image-algebra-derived-category). -/
def directImageAlgebraDerivedQCohProperty (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ObjectProperty (DerivedCategory (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace f)))) :=
  fun K ↦ ∀ n : ℤ,
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) n).obj K).IsQuasicoherent

/-- The full subcategory `D_QCoh(f_* O_X)` of the derived category of modules over the
ring sheaf `f_* O_X` whose cohomology sheaves are quasi-coherent over that ring sheaf.
Source: Stacks, Tag 0AVW (blueprint: def-sc-direct-image-algebra-derived-category). -/
abbrev directImageAlgebraDerivedQCohCategory (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :=
  (directImageAlgebraDerivedQCohProperty f).FullSubcategory

end AlgebraicGeometry
