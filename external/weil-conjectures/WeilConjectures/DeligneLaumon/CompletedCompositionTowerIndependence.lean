/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization

/-! # Common-refinement equality for completed tower components

Source: Stacks 0F7J, the six-square comparison of two compactification towers.
(blueprint: lem-zl-completed-composition-tower-independence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))

/-- Transport of a single completed tower map to three specified compactifications.
Every factor is supplied explicitly; no choice of an unproved witness is made.
Source: Stacks 0F7J (blueprint: lem-zl-completed-composition-tower-independence). -/
def sfCompletedCompositionTransport
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : DerivedCategory (scalarReductionSource l E X))
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K)))
    (hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K) hη))
    (ρf : (image (completed l E) e.restrict).obj K ≅ (image (completed l E) cf).obj K)
    (ρg : (image (completed l E) d).obj ((image (completed l E) e.restrict).obj K) ≅
      (image (completed l E) cg).obj ((image (completed l E) e.restrict).obj K))
    (ρfg : (image (completed l E) (d.comp e)).obj K ≅ (image (completed l E) cfg).obj K) :
    (image (completed l E) cg).obj ((image (completed l E) cf).obj K) ⟶
      (image (completed l E) cfg).obj K :=
  (image (completed l E) cg).map ρf.inv ≫ ρg.inv ≫
    sfCompletedCompositionOnTower l E d e K hη hLambda ≫ ρfg.hom

variable
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))] [Z.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Z ↘ Spec (.of K₀))] [QuasiCompact (Z ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [g.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

include hl in
/-- The transported completed arrows agree, conditional on the local normalizations.
This asserts an equality of already constructed morphisms, with no existence or
invertibility conclusion for a compositor.
Source: Stacks 0F7J, independence-of-choices proof
(blueprint: lem-zl-completed-composition-tower-independence).

Proof: take a common refining compatible tower and equalize parallel refinement
arrows. In its comparison with either original tower label the six proper/open
squares A,B,C,D,E,F as in Stacks 0F7J. Horizontal pasting gives the comparison for E
from F and A; vertical pasting gives the equality for B,F and C,D. Naturality of B
moves the A comparison through the middle proper/open map. Insert the canonical
proper and open compositors, use their associativity, and cancel adjacent inverse
refinement factors. These equalities hold on strict systems before realization.
The normalized completed realization preserves those equations and identifies each
refinement factor with the one in SfCompletedRefinementSpec: transpose under the
open adjunction, where its normalization fixes the map, then use faithfulness.
Consequently both displayed transported arrows equal the transported map of the
common tower. No faithfulness of finite derived evaluation is used. Identical
towers with different normalized witnesses are included in the argument. -/
theorem sfCompletedCompositionTransport_independent
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : sfIntegralConstructibleCategory l E X)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (rf : e.restrict.Refinement cf) (rg : d.Refinement cg)
    (rfg : (d.comp e).Refinement cfg)
    (hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj)))
    (hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i)
      e.restrict.g e.g d.i e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj) hη))
    (ρf : (image (completed l E) e.restrict).obj K.obj ≅
      (image (completed l E) cf).obj K.obj)
    (ρg : (image (completed l E) d).obj
        ((image (completed l E) e.restrict).obj K.obj) ≅
      (image (completed l E) cg).obj ((image (completed l E) e.restrict).obj K.obj))
    (ρfg : (image (completed l E) (d.comp e)).obj K.obj ≅
      (image (completed l E) cfg).obj K.obj)
    (hf : SfCompletedRefinementSpec l E rf K.obj ρf)
    (hg : SfCompletedRefinementSpec l E rg
      ((image (completed l E) e.restrict).obj K.obj) ρg)
    (hfg : SfCompletedRefinementSpec l E rfg K.obj ρfg)
    (d' : Compactification g) (e' : Compactification (f ≫ d'.i))
    (rf' : e'.restrict.Refinement cf) (rg' : d'.Refinement cg)
    (rfg' : (d'.comp e').Refinement cfg)
    (hη' : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e'.g d'.i)).unit.app
      ((openExtension (completed l E) e'.restrict.i).mapDerivedCategory.obj K.obj)))
    (hLambda' : IsIso (sfCompositionLambda l E (pullback.fst e'.g d'.i)
      e'.restrict.g e'.g d'.i e'.isPullback_restrict.w.symm
        ((openExtension (completed l E) e'.restrict.i).mapDerivedCategory.obj K.obj) hη'))
    (ρf' : (image (completed l E) e'.restrict).obj K.obj ≅
      (image (completed l E) cf).obj K.obj)
    (ρg' : (image (completed l E) d').obj
        ((image (completed l E) e'.restrict).obj K.obj) ≅
      (image (completed l E) cg).obj ((image (completed l E) e'.restrict).obj K.obj))
    (ρfg' : (image (completed l E) (d'.comp e')).obj K.obj ≅
      (image (completed l E) cfg).obj K.obj)
    (hf' : SfCompletedRefinementSpec l E rf' K.obj ρf')
    (hg' : SfCompletedRefinementSpec l E rg'
      ((image (completed l E) e'.restrict).obj K.obj) ρg')
    (hfg' : SfCompletedRefinementSpec l E rfg' K.obj ρfg')
    : sfCompletedCompositionTransport l E cf cg cfg K.obj d e hη hLambda ρf ρg ρfg =
      sfCompletedCompositionTransport l E cf cg cfg K.obj d' e' hη' hLambda' ρf' ρg' ρfg' := by
  sorry

end WeilConjectures
