/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.FiniteStageRationalExchangeData

import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.RationalOperationCoherence
import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.RationalSquareExchangeCoherence

/-! # Finite-stage rational exchange and its coefficient coherence

Source: sketch32, lines 1191--1228, 1262--1279 and 1291--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence).

The raw composites and exchange are the already published `sbcRationalLeft`,
`sbcRationalRight` and `sbcRationalExchange`. The witness propositions below specify
individual operations, canonical tensor comparisons, their units and towers, and
both raw and finite-stage Karoubi exchange equations. They are conclusions, not
additional hypotheses. No constructible landing or invertibility is required.

## Main definitions

* `rawPull`, `rawPush`: the existing localization applied to the actual operations.
* `HasOperationCoherence`: canonical comparisons, units and towers for one operation pair.
* `HasCoherence`: the four operation pairs and their coefficient-compatible exchange.

## Main statements

* `between_karoubi_spec`: the additive pure-tensor extension formula.
* `additive_karoubi_extension_spec`: supported Karoubi formulas, including comparisons.
* `finiteStageRationalExchangeCoherence`: the full finite-stage conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures TensorProduct

namespace CategoryTheory.ScalarLocalization

universe r a b x y
variable (R : Type r) [CommRing R] (t : R)
  {C : Type a} [Category.{x} C] [Preadditive C] [Linear R C]
  {D : Type b} [Category.{y} D] [Preadditive D] [Linear R D]
  (H : C ⥤ D) [H.Additive] [H.Linear R]

end CategoryTheory.ScalarLocalization

namespace CategoryTheory.Idempotents

universe a b x y
variable {A : Type a} [Category.{x} A] [Preadditive A]
  {B : Type b} [Category.{y} B] [Preadditive B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]

end CategoryTheory.Idempotents

attribute [local irreducible] pbcAmbientCompleteRawSystem

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
