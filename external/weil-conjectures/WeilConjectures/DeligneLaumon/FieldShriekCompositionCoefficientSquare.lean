/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.DeligneLaumon.IntegralCompositionCoefficientSquare

/-! # Coefficient compatibility of normalized compact-support compositors

The scalar square in step 7 of the field shriek composition argument, before descent.
Source: Stacks 0F7J and Bhatt--Scholze, Definition 6.7.6.
(blueprint: lem-zl-field-shriek-composition-coefficient-square).
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
open PurCompactSupport GeneralAlgebraicallyClosedCoefficients

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem comp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX
  cases hY
  cases hZ
  cases hf
  cases hg
  rfl

private theorem app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (α.app X) (α.app X') := by
  cases h
  rfl

private theorem scalar_obj (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (K : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K.obj⟩ :=
  (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K

private theorem scalar_map (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    {K K' : sfIntegralConstructibleCategory l E W} (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((sfRationalConstructibleLocalization l E W).map f))
      ((sfRationalConstructibleLocalization l L W).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map f)) := by
  simpa only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, map_one] using
    (sfRationalScalarExtension_existsUnique l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 K K' f 1

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Sf : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cf)
  (Sg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cg)
  (Sfg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cfg)
  (B : ∀ E₀ : Padic.FiniteCoefficientFields l Ω,
    sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cf
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) ⋙
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀) ≅
    sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cfg
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀))

end WeilConjectures
