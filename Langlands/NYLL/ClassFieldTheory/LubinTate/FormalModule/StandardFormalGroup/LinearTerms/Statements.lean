/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: extract the signatures of the seven
source theorems M354.001-M354.007 (source lines 53-188 of
StandardFormalGroup.lean, upstream commit
fbd320cd8b1b06487c58227e92eb135794267709) as reducible Prop-valued
targets named `<adapted source name>Statement`. Prefix the namespaces with
Langlands.NYLL; the two private source theorems become the targets
Langlands.NYLL.PortInternal.M354.d003Statement and d005Statement. Import
the published linear-term definitions and Mathlib's multivariable
substitution module instead of the full source imports. Keep the source
section variables, universes, binders, hypotheses, local classical
decidability and conclusions; omit the proofs and disable the
unused-variable linter only on targets whose hypotheses are not used by the
conclusion. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Targets for the linear-term calculus of the standard formal group

Exact proposition targets for the seven linear-term theorems at the start of
the source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup`:
coefficients of total degree below two agree with the prescribed linear
form, the coefficient of `X_i` is `L i`, a weighted sum of linear forms is
a linear form, substitution composes linear coefficient matrices, the
basis-vector linear form is a variable, a variable has the basis-vector
linear term, and zero has the zero linear term. Nothing is proved here.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe w w'

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

section LinearTerms

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

namespace HasLinearTerm

set_option linter.unusedVariables false in
/-- Target of M354.001 (`HasLinearTerm.coeff_eq_linearForm`, source line 53):
in total degree less than two, a series with prescribed linear term agrees
coefficientwise with that linear form. -/
abbrev coeff_eq_linearFormStatement
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : d.degree < 2) : Prop :=
  MvPowerSeries.coeff d H =
    MvPowerSeries.coeff d (linearForm L)

set_option linter.unusedVariables false in
/-- Target of M354.002 (`HasLinearTerm.coeff_single`, source line 67): the
coefficient of `X_i` is the prescribed coefficient `L i`. -/
abbrev coeff_singleStatement
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L) (i : σ) : Prop :=
  MvPowerSeries.coeff (Finsupp.single i 1) H = L i

set_option linter.unusedVariables false in
/-- Target of M354.004 (`HasLinearTerm.subst`, source line 90): substituting
series with prescribed linear terms `M i` into a series with prescribed
linear term `L` gives the linear term `fun j => ∑ i, L i * M i j`. -/
abbrev substStatement
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    {G : σ → MvPowerSeries τ R} {M : σ → τ → R}
    (hG : ∀ i, HasLinearTerm (G i) (M i)) : Prop :=
  HasLinearTerm (MvPowerSeries.subst G H)
    (fun j => ∑ i, L i * M i j)

end HasLinearTerm

/-- Target of M354.006 (`hasLinearTerm_X`, source line 179): a variable has
the corresponding standard-basis linear term. -/
abbrev hasLinearTerm_XStatement (i : σ) : Prop :=
  HasLinearTerm (MvPowerSeries.X i : MvPowerSeries σ R)
    (fun j => if j = i then (1 : R) else 0)

/-- Target of M354.007 (`hasLinearTerm_zero`, source line 186): zero has
zero linear term. -/
abbrev hasLinearTerm_zeroStatement : Prop :=
  HasLinearTerm (0 : MvPowerSeries σ R) (fun _ => 0)

end LinearTerms

end SameUniformizer
end Langlands.NYLL.LubinTate

namespace Langlands.NYLL.PortInternal.M354

open Langlands.NYLL.LubinTate.SameUniformizer

section LinearTerms

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

/-- Target of M354.003 (private source theorem
`LubinTate.SameUniformizer.HasLinearTerm.linearForm_weighted_sum`, source
line 76): a weighted sum of linear forms is the linear form of the
weighted coefficients. -/
abbrev d003Statement (L : σ → R) (M : σ → τ → R) : Prop :=
  (∑ i, MvPowerSeries.C (L i) * linearForm (M i)) =
    linearForm (fun j => ∑ i, L i * M i j)

/-- Target of M354.005 (private source theorem
`LubinTate.SameUniformizer.linearForm_basis`, source line 171): the
standard-basis linear form is the corresponding variable. -/
abbrev d005Statement (i : σ) : Prop :=
  linearForm (R := R)
      (fun j : σ => if j = i then (1 : R) else 0) =
    (MvPowerSeries.X i : MvPowerSeries σ R)

end LinearTerms

end Langlands.NYLL.PortInternal.M354
