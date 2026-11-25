/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization

/-! # Invertibility of the completed proper/open tower map

Source: Stacks 0F7J; Bhatt--Scholze Definition 6.7.6 and Lemmas 6.7.7, 6.1.13.
(blueprint: lem-zl-completed-composition-tower-is-iso).
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
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))] [Z.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Z ↘ Spec (.of K₀))] [QuasiCompact (Z ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [g.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

include hl in
/-- The actual proper/open map on one tower is invertible on integral inputs.
Source: Stacks 0F7J and Bhatt--Scholze Definition 6.7.6, Lemmas 6.7.7 and 6.1.13
(blueprint: lem-zl-completed-composition-tower-is-iso).

Proof: extension by zero is fully faithful, so the open unit is invertible.
Proper base change for the cartesian square e.isPullback_restrict identifies
Lambda with the restriction exchange followed by this inverse unit. On the
strict derived reduction system its components are the finite proper/open
isomorphisms on the bounded constructible etale origins of K. Derived-complete
conservativity makes Lambda invertible. Its inverse open adjunct Gamma has those
same finite proper/open reductions. Open extension and proper direct image keep
the completed constructible domain, so the cone of Gamma is complete; its zero
reductions make it zero. Thus Gamma is invertible. The remaining factors of
sfCompletedCompositionOnTower are functorial images of the canonical proper and
open compositors and the equality e.restrict_i_fst. All are invertible, so their
composite is invertible. This includes zero inputs and empty schemes. -/
theorem sfCompletedCompositionOnTower_isIso
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : sfIntegralConstructibleCategory l E X) :
    ∃ hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj)),
    ∃ hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
        e.isPullback_restrict.w.symm
          ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj) hη),
      IsIso (sfCompletedCompositionOnTower l E d e K.obj hη hLambda) := by sorry

end WeilConjectures
