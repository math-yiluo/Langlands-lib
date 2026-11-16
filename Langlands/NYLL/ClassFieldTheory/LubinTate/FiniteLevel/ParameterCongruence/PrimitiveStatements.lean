/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 323, 2026-11-16: extract only the types of M392.003–005
(source lines 72–144) at commit fbd320cd8b1b06487c58227e92eb135794267709
as closed, unproved Prop-valued targets; prefix the namespace with
Langlands.NYLL, add Statement suffixes, and use focused imports of the
published primitive-polynomial definition and Mathlib evaluation API.
See the paired Markdown for the complete adaptation record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Parameter congruence targets for primitive Lubin--Tate polynomials

These three targets extract the theorem types of M392.003–005 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`.
They concern coefficient maps, evaluation equality, and evaluation
congruence modulo an arbitrary ideal, using the published primitive polynomial.
-/

universe u v w

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

set_option linter.unusedVariables false in
/-- M392.003 target: equal parameter images give equal images of the
primitive quotient polynomials at every finite level. -/
def standardLubinTatePrimitivePolynomial_map_eq_of_parameter_eqStatement : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ) (n : ℕ),
    (standardLubinTatePrimitivePolynomial F π n).map f =
      (standardLubinTatePrimitivePolynomial F ϖ n).map f

set_option linter.unusedVariables false in
/-- M392.004 target: equal parameter images give equal evaluations of
the primitive quotient polynomials at every point of the target ring. -/
def standardLubinTatePrimitivePolynomial_eval₂_eq_of_parameter_eqStatement : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ)
    (n : ℕ) (x : R),
    Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F π n) =
      Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F ϖ n)

set_option linter.unusedVariables false in
/-- M392.005 target: parameters congruent modulo an ideal after mapping
give congruent evaluations of their primitive quotient polynomials. -/
def standardLubinTatePrimitivePolynomial_eval₂_sub_mem_of_parameter_sub_memStatement : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R) (I : Ideal R)
    {π ϖ : F.valuationSubring} (h : f π - f ϖ ∈ I)
    (n : ℕ) (x : R),
    Polynomial.eval₂ f x
          (standardLubinTatePrimitivePolynomial F π n) -
        Polynomial.eval₂ f x
          (standardLubinTatePrimitivePolynomial F ϖ n) ∈ I

end Langlands.NYLL.LubinTate
