/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.InducedCategory
public import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange

/-! # Affine-coordinate comparison data
Source: Stacks Project, Tags 08DW, 06Y1 and 0D5S.
(blueprint: def-pc-affine-coordinate-comparison-data). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- An affine coordinate and its specified localized tilde functor. All data are supplied.
Source: the affine-coordinate square in Stacks, Tag 08DW(2).
(blueprint: def-pc-affine-coordinate-comparison-data). -/
structure AffineComparisonCoordinate where
  A : CommRingCat.{u}
  X : Scheme.{u}
  σ : Spec A ≅ X
  d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X
  hd : DerivedCategory.Q ⋙ d.functor ≅
    (@Functor.mapHomologicalComplex ℤ
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
      (SheafOfModules.pushforward σ.hom.toRingCatSheafHom)
      ⟨fun _ _ ↦ rfl⟩ (.up ℤ)) ⋙ DerivedCategory.Q
  H : CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory X
  hH : H ≅
    (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) _ _ _ _
      (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
        (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙ d.functor

/-- The acyclic-tensor criterion for a supplied model; no model is chosen.
Source: Stacks Project, Tag 06Y1.
(blueprint: def-pc-affine-coordinate-comparison-data). -/
abbrev AffineComparisonKFlat (A : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
    (CochainComplex.mapBifunctor L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} A))).Acyclic

/-- Comparison on the full category of two labelled models, including cross morphisms.
Source: Stacks Project, Tag 08DW(2), natural affine comparison.
(blueprint: def-pc-affine-coordinate-comparison-data). -/
abbrev AffineCoordinateComparisonFamily : Type _ :=
  ∀ (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A) (p : b.X ⟶ a.X),
    b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom →
    ∀ (M N : CochainComplex (ModuleCat.{u} a.A) ℤ),
      AffineComparisonKFlat a.A M → AffineComparisonKFlat a.A N →
      (inducedFunctor (fun q : Bool ↦ cond q M N) ⋙
        (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ b.H ≅
      inducedFunctor (fun q : Bool ↦ cond q M N) ⋙ a.H ⋙ derivedPullback p)

end AlgebraicGeometry
