/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro

/-! # Saturated multiplicative systems and pointwise left-derived values

Source: Stacks Project, Categories, Tags 04VC, 05Q8, 05Q4; Derived Categories,
Tags 05R2, 05S8, 05S9 (blueprint: def-pur-saturated-triangulated-localization).

## Main definitions

* `MorphismProperty.IsMultiplicativeSystem`: MS1--MS3.
* `MorphismProperty.IsSaturatedMultiplicativeSystem`: MS1--MS4.
* `MorphismProperty.IsSaturatedTriangulatedMultiplicativeSystem`: MS1--MS6.
* `Functor.IsStrictLocalizationAt`: the strict universal property on functors and transformations.
* `Functor.IsTriangulatedLeftDerivedValue`: a value of the essentially constant pro-diagram.
* `Functor.IsTriangulatedLeftDerivedDefinedAt`: existence of such a value.
-/

@[expose] public section

universe u v uD vD uE vE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace MorphismProperty

/-- A multiplicative system satisfies both fraction-calculus axioms: identities and composition
(MS1), the two square completions (MS2), and the two cancellation conditions (MS3).
Source: Stacks Project, Categories, Tag 04VC
(blueprint: def-pur-saturated-triangulated-localization). -/
def IsMultiplicativeSystem {C : Type u} [Category.{v} C] (S : MorphismProperty C) : Prop :=
  S.HasLeftCalculusOfFractions ∧ S.HasRightCalculusOfFractions

/-- A saturated multiplicative system satisfies MS1--MS3 and MS4: if `h ≫ g` and `g ≫ f`
belong to `S`, then `g` belongs to `S`.
Source: Stacks Project, Categories, Tag 05Q8
(blueprint: def-pur-saturated-triangulated-localization). -/
def IsSaturatedMultiplicativeSystem {C : Type u} [Category.{v} C]
    (S : MorphismProperty C) : Prop :=
  S.IsMultiplicativeSystem ∧
    ∀ (A B C' D : C) (h : A ⟶ B) (g : B ⟶ C') (f : C' ⟶ D),
      S (g ≫ f) → S (h ≫ g) → S g

/-- A saturated multiplicative system compatible with the triangulation: MS1--MS4 together
with shift invariance (MS5) and completion of a square of distinguished triangles by a third
map in `S` (MS6). Integer-shift compatibility is equivalent to the Stacks shift-by-one iff.
Source: Stacks Project, Derived Categories, Tags 05R2 and 05S8
(blueprint: def-pur-saturated-triangulated-localization). -/
def IsSaturatedTriangulatedMultiplicativeSystem {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    (S : MorphismProperty C) : Prop :=
  S.IsSaturatedMultiplicativeSystem ∧ S.IsCompatibleWithTriangulation

end MorphismProperty

namespace Functor

/-- The localization universal property, strict on functors and natural transformations.
For every target category, functors inverting `S` factor uniquely through `Q`, and whiskering
with `Q` is bijective on natural transformations. Target universes are arbitrary parameters.
Source: Stacks Project, Categories, localization section (Tag 04VB)
(blueprint: def-pur-saturated-triangulated-localization). -/
def IsStrictLocalizationAt {C : Type u} {D : Type uD}
    [Category.{v} C] [Category.{vD} D] (Q : C ⥤ D) (S : MorphismProperty C) : Prop :=
  S.IsInvertedBy Q ∧ ∀ (E : Type uE) (_ : Category.{vE} E),
    Nonempty (Localization.StrictUniversalPropertyFixedTarget Q S E) ∧
      ∀ G G' : D ⥤ E, Function.Bijective (fun α : G ⟶ G' ↦ whiskerLeft Q α)

/-- In Situation 05S8, `Y` is a value of `LF` at `X` exactly when the diagram on `S/X`,
sending `s : X' ⟶ X` to `F(X')`, is essentially constant as a pro-object with value `Y`.
`S.Over ⊤ X` has all commuting triangles as morphisms; no denominator condition is imposed
on these morphisms. Cofilteredness is included in `IsEssentiallyConstantProDiagram`.
Source: Stacks Project, Categories, Tag 05Q4; Derived Categories, Tags 05S8 and 05S9(2)
(blueprint: def-pur-saturated-triangulated-localization). -/
def IsTriangulatedLeftDerivedValue {C : Type u} {D : Type uD}
    [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (S : MorphismProperty C)
    (_hS : S.IsSaturatedTriangulatedMultiplicativeSystem) (X : C) (Y : D) : Prop :=
  IsEssentiallyConstantProDiagram
    (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F) Y

/-- In Situation 05S8, the left derived functor is defined at `X` if its denominator
pro-diagram is essentially constant with some value `Y`.
Source: Stacks Project, Derived Categories, Tag 05S9(2)
(blueprint: def-pur-saturated-triangulated-localization). -/
def IsTriangulatedLeftDerivedDefinedAt {C : Type u} {D : Type uD}
    [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem) (X : C) : Prop :=
  ∃ Y : D, F.IsTriangulatedLeftDerivedValue S hS X Y

end Functor

end CategoryTheory
