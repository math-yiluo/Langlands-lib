/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Targets: norms of finite cyclic representations and iterates of the action

Modified by Worker 5264, 15 November 2026: state the source theorems
M043.009 `rep_norm_eq_generatorPowerSum`, M043.010
`rep_action_pow_eq_iterate`, M043.011 `rep_norm_eq_generatorIterateSum` and
M043.012 `rep_action_pow_fixed` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by the published
`IntegralRepGroupType` module and the Mathlib module of `Rep.norm`, keep the
source opens of `CategoryTheory` and `BigOperators`, binders and statements
unchanged, and omit the proofs, the source universe declaration, the opens
of `KummerTheory` and `CyclicCohomology` (none of their names occur in these
statements) and the rest of the source file, and turn off the unused-variable
linter for M043.009, M043.011 and M043.012, whose hypotheses `hg`, `hcard`,
`hf` and `hx` the propositions do not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

open CategoryTheory
open scoped BigOperators

set_option linter.unusedVariables false in
/-- Target: enumerate the norm of a finite cyclic representation by the first
n powers of a specified generator. -/
def rep_norm_eq_generatorPowerSumStatement
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n) (x : B.V) : Prop :=
    B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x

/-- Target: powers in a representation are the iterates of the corresponding
action map. -/
def rep_action_pow_eq_iterateStatement {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) : Prop :=
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x

set_option linter.unusedVariables false in
/-- Target: replace the generator action in the preceding norm formula by a
pointwise equal endomorphism and enumerate its iterates. -/
def rep_norm_eq_generatorIterateSumStatement
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n)
    (f : B.V → B.V) (hf : ∀ z, B.ρ g z = f z) (x : B.V) : Prop :=
    B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x

set_option linter.unusedVariables false in
/-- Target: every nonnegative power fixes an element fixed by the original
group element. -/
def rep_action_pow_fixedStatement {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) : Prop :=
    B.ρ (g ^ n) x = x

end

end Langlands.NYLL.ClassFormation
