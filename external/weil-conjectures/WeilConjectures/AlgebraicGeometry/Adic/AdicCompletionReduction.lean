/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicReductionAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulQuotientLimit
import WeilConjectures.AlgebraicGeometry.Adic.AdicReductionAdjunction
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NilpotentKoszulCompletionUnit

/-!
# Reduction of adic completion

Source: Weil conjectures blueprint, proper base change, order 1260,
`lemma-weil-pbc-adic-completion-reduction.md`
(blueprint: lemma-weil-pbc-adic-completion-reduction).

The completion object and its evaluation are those of the landed strict product-cone
construction. Its reduction is computed on an arbitrary K-flat model of that object.
The comparison is defined by the derived scalar adjunction, using its unit, so the
isomorphism assertion concerns the specified evaluation map. Positive level a is n+1.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Evaluation from the specified strict product-cone limit at level n+1.
Source: order 1260, statement (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionEvaluation (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) :
    adicCompletionObject X d M ⟶ adicReductionSequence X d M n :=
  (adicLocalization X Λ).map
    (adicCompletionProjection X d M ≫ Pi.π (adicReductionComplex X d M) n)

set_option linter.style.haveILetI false in
set_option linter.style.haveILetI false
end AlgebraicGeometry.Scheme
