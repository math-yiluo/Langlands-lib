/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionIntegralComponent
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersion

/-! # Naturality of normalized integral shriek components

Source: Stacks Project, Tag 0F7J, and Bhatt--Scholze Definition 6.7.6
(blueprint: lem-zl-field-shriek-integral-component-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

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

/-- Normalized integral composition components commute with an arbitrary input map.
Source: Stacks 0F7J, naturality of the proper/open construction; Bhatt--Scholze
Definition 6.7.6 (blueprint: lem-zl-field-shriek-integral-component-naturality).

Proof: express both normalized components on a single compatible tower refining the
three supplied compactifications. The open unit, restriction exchange, proper counit
and their adjunct Gamma are natural in the input, as are the proper and open
compositors. Each normalized refinement comparison is natural because transposition
under its open adjunction turns its naturality square into naturality of the proper
counit and open unit. Finally the Roos realization comparisons are natural on all
morphisms, including derived roofs. Paste these squares, cancel the intermediate
isomorphisms, and apply faithfulness of the integral constructible inclusion. The
result is the displayed equation for the original arbitrary input morphism. No
faithfulness assertion for finite derived evaluations is used. -/
theorem sfFieldShriekCompositionIntegral_component_naturality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {K L : sfIntegralConstructibleCategory l E X}
    (a : (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K)
      ⟶ (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E).obj K)
    (b : (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj L)
      ⟶ (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E).obj L)
    (ha : SfIntegralCompositionComponentSpec D l hl cf cg cfg E K a)
    (hb : SfIntegralCompositionComponentSpec D l hl cf cg cfg E L b)
    (v : K ⟶ L) :
    (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).map
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (coefficientPrimeUnit l D hl) cf E).map v) ≫ b =
      a ≫ (sfCompactSupportFiniteIntegralFunctor l D.k
        (coefficientPrimeUnit l D hl) cfg E).map v := by
  sorry

end WeilConjectures
