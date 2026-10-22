# Local-constant systems in one common algebraic closure

This module specifies Deligne's four local-constant laws on the actual
common-closure inputs constructed in `LocalFactor.CommonClosure`. It neither
proves existence nor chooses a system. Its base is a finite p-adic field `F`;
its indices are all finite intermediate fields of the specified algebraic
closure of `F`, including nonnormal ones. It is a common-closure formulation,
not the global isomorphism-invariant function on all sextuples in Deligne 4.1.
Comparison across base fields and algebraic closures is a separate obligation.

## The assignment and its laws

`Assignment F` assigns a complex unit to each intermediate field `E`, continuous
nontrivial unitary additive character, regular additive Haar measure, and element
of the continuous exact Grothendieck group. It is a function type with no laws or
chosen element. Representations have carrier universe `max uF uV`, which is
closed under the actual induction construction. The quotient already identifies
isomorphic representations and imposes all short exact sequence relations.

`AdditiveRelation` requires the value at `x + y` to be the product of the values.
The intrinsic lemmas `value_zero` and `value_neg` use cancellation in complex
units to obtain the value one at zero and inverse at a negative class.
`value_shortExact` rewrites the published defining relation of the exact quotient
and applies additivity, giving precisely the multiplicative law for a genuine
short exact sequence. It uses no semisimplicity or equivariant splitting.

`positiveScale c hc` is the complex unit whose value is the strictly positive
finite real number `c`. `HaarScalingRelation` uses the actual measure scaling
constructor and the integer power `c ^ degree(x)`. Negative dimensions therefore
use inverse powers. Quantification over positive `NNReal` scalars covers exactly
all finite strictly positive real scalars.

`InductionRelation` quantifies over every actual inclusion `E.field ≤ L.field`,
every additive character on `E`, arbitrary Haar measures on both fields, and
every element of the actual dimension-zero kernel over `L`. Its two sides are
values on the constructed exact induction and on the original class with the
actual trace-pulled character. The degree-zero condition is essential; no
unrestricted induction identity or lambda factor is substituted. Characteristic
zero makes these finite extensions separable. Haar independence is incorporated
by quantifying over both measures, as in Tate 3.4.1 and 3.4.8.

`RankOneRelation` pulls each field quasicharacter back through the supplied
common-closure reciprocity component, inserts its actual continuous scalar line
in the exact quotient, and compares the value with
`fieldData.abelianEpsilonExpression`. The latter is the existing convergent
Gauss integral in the ramified case and the existing valuation/volume expression
in the unramified case. Equality is taken in the complex numbers, because the
abelian expression's nonvanishing is not yet an unconditional theorem.
`abelianExpression_ne_zero` proves that a supplied system implies that
nonvanishing, by rewriting to the value of a complex unit.

`IsSystem` conjoins the full `NormalizedReciprocity` condition with these four
laws. Thus an arbitrary reciprocity equivalence is never described as canonical.
`Exists e` states that a normalized supplied reciprocity family admits a system;
`Unique e` compares any two systems for the same family. Both are Prop-valued
definitions only. There is no inhabitant, choice, axiom, or proof of either claim.

## Source correspondence and scope

The primary source is Pierre Deligne, *Les constantes des equations fonctionnelles
des fonctions L* (1973), theorem 4.1, retained PDF/internal page 35, printed page
535. Literature ID: `deligne-1973-local-constants`; SHA256:
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The original page was visually checked. Its conditions (1), (2), (3), (4)
correspond respectively to exact multiplicativity, positive Haar scaling,
degree-zero induction with trace, and rank-one agreement. Deligne first
formulates the function on isomorphism classes of sextuples containing the field,
its algebraic closure and all the other inputs. This module fixes the field and
closure and imposes these four laws on their actual finite-intermediate-field
family; it does not assert the additional global isomorphism descent.

John Tate, *Number theoretic background* (1979), sections 2.3.2 and 3.4.1–3.4.3,
3.4.8, printed pages 11–12 and 14–15 (retained Part II PDF pages 20–21 and 23–24),
gives the corresponding exact-virtual and common-extension-family formulation.
Literature ID: `tate-1979-number-theoretic-background`; SHA256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The abelian construction used here is Tate 3.2.6 as documented in
`LocalFactor.Abelian.Definitions`. These are Deligne's measure-dependent constants;
Tate 3.6.1 introduces a distinct half-twisted, self-dual-measure convention.
Neither spectral twisting nor that change of convention is made in this module.

The quantifiers deliberately specialize the cited local-field statements to
finite extensions of `Q_p`, complex coefficients, the existing nontrivial unitary
additive characters, and one fixed pair of field/representation universes. No
archimedean, positive-characteristic, closure-comparison, carrier-universe
comparison, or global existence assertion is hidden in the names. The intrinsic
proofs use the published exact quotient and elementary unit-group algebra.
