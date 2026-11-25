/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-! # The localizing closure of perfect complexes

Source: Stacks Project, Derived Categories of Schemes, Theorem 09IS
(`perfect.tex`, theorem-bondal-van-den-Bergh), and Derived Categories, Lemma 09SN
(`derived.tex`, lemma-write-as-colimit) (blueprint: def-pc-perfect-localizing-closure).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry



/-- The smallest strictly full subcategory of `D_QCoh(𝒪_X)` containing every perfect
 complex and closed under shifts, cones, retracts, and arbitrary set-indexed coproducts
Source: Stacks Project, Theorem 09IS and Lemma 09SN.
(blueprint: def-pc-perfect-localizing-closure). -/
def perfectLocalizingClosure (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ObjectProperty (schemeDerivedQCohCategory X) :=
  sInf {P : ObjectProperty (schemeDerivedQCohCategory X) |
    (∀ E : schemeDerivedQCohCategory X,
      Scheme.perfectSubcategory X E.obj → P E) ∧
    (∀ (A B : schemeDerivedQCohCategory X), P A → Nonempty (A ≅ B) → P B) ∧
    (∀ (A : schemeDerivedQCohCategory X) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory X),
        Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory X), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory X)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory X), Nonempty (T.obj₃ ≅ C.obj) → P C) ∧
    (∀ (A B : schemeDerivedQCohCategory X), P B →
      Nonempty (Retract A.obj B.obj) → P A) ∧
    (∀ (J : Type u) (E : J → schemeDerivedQCohCategory X),
      ∀ (S : schemeDerivedCategory X) (ι : ∀ j, (E j).obj ⟶ S),
        IsColimit (Cofan.mk S ι) →
        ∀ (B : schemeDerivedQCohCategory X), Nonempty (B.obj ≅ S) →
          (∀ j, P (E j)) → P B) }

end AlgebraicGeometry
