# Exact algebraic separation of gamma factors

Worker 468 proves the closed theorem `Langlands.Global.gammaSeparation` with
exact type `Langlands.Global.GammaSeparationStatement`, the unchanged Library
conjunction in `SeparationStatement.lean`. Its two public components are
`gammaPolynomialSeparation` and `reflectedRootRegion` in the same namespace.
All parameters, the four normalizations, both separate noncancellation
hypotheses, the integer exponents and all three equality conclusions are
retained.

## Four-polynomial separation

Write `ι` for the embedding of complex polynomials in `RatFunc ℂ`, and let
`ρ` be the published involutive algebra homomorphism substituting
`X ↦ δ/X`, where `δ` is the unit with value `q⁻¹`. The proof verifies that this
variable is exactly the target's `(RatFunc.C q)⁻¹ * RatFunc.X⁻¹`. Put
`U = a X^m` and `V = c X^k`. Nonzero normalization and the injectivity of the
polynomial embedding and reciprocal substitution ensure that both reflected
denominators are nonzero. Clearing the actual rational-function identity gives

\[
  \iota(P)\,[U\rho(\iota(Q_{\rm dual}))]
   =\iota(Q)\,[V\rho(\iota(P_{\rm dual}))].
\]

The private `dvd_of_regular_cross` proves a general divisibility implication
from an identity `ι(P) R = ι(Q) S`. It assumes `P(0) ≠ 0`, regularity of `R`
and `S` at all nonzero complex points, and that `S` evaluates nonzero at any
nonzero root of `P`. Here regularity is the existing `RationalEvaluation.RegularAt`
predicate on the reduced rational denominator.

Its proof is strong induction on `P.natDegree`. A degree-zero `P` is a nonzero
constant and divides every polynomial. Otherwise the fundamental theorem of
algebra gives a root `z`; `P(0) ≠ 0` makes `z` nonzero. The published regular
multiplication evaluation lemma applied to the cross identity shows that `z`
is also a root of `Q`, since `S(z) ≠ 0`. Factor `X - C z` out of both
polynomials, cancel its nonzero rational image, and apply induction to the
quotients. The new first polynomial still has nonzero value at zero, and its
roots are roots of `P`. Its degree decreases by one. This successive factor
cancellation preserves root multiplicities.

For the displayed cross identity, `monomial_regular_nonzero` uses the published
regularity and evaluation lemmas for integer powers to prove that `U` and `V`
are regular and nonzero at every nonzero point. The published `regular_subst`
and `eval_subst` give regularity of the reflected polynomials and their exact
values at `q⁻¹ z⁻¹`. The separate no-common-root hypothesis for `P,Pdual`
therefore gives `P ∣ Q`; the separate hypothesis for `Q,Qdual` gives `Q ∣ P`.
The private `eq_of_normalized_dvd_dvd` shows that mutual divisibility and value
one at zero give equality: the quotient has degree zero, and evaluation at
zero makes that constant one. Thus `P = Q`.

Canceling this common nonzero polynomial leaves

\[
 U\rho(\iota(Q_{\rm dual}))=V\rho(\iota(P_{\rm dual})).
\]

Apply `ρ` and its published involution law to obtain

\[
 \iota(P_{\rm dual})\rho(V)=\iota(Q_{\rm dual})\rho(U).
\]

At a nonzero point, `ρ(U)` and `ρ(V)` are regular and nonzero by the same
published substitution lemmas evaluated at the nonzero point `δ/z`. The
divisibility helper now applies in both directions without any further root
assumption. Normalization gives `Pdual = Qdual`. Finally, cancel the common
nonzero reflected polynomial from the remaining identity to obtain `U = V`,
exactly equality of the epsilon rational monomials in the target.

Evaluation is applied only to identities between products with established
regularity. The original gamma quotients are never evaluated at a possible
pole.

## Reciprocal root regions

Suppose both root equations hold at a nonzero `z`. The two given lower bounds
and the norm of the reflected argument give

\[
 r\leq\lVert z\rVert,\qquad
 r^{-1}\leq q^{-1}/\lVert z\rVert.
\]

Since `r > 0` and `z ≠ 0`, multiplication yields
`1 ≤ r⁻¹ ‖z‖ ≤ q⁻¹`. The assumption `q > 1` gives `q⁻¹ < 1`, a contradiction.
This proves `reflectedRootRegion` with exactly the published quantifiers.
`gammaSeparation` pairs the two component proofs.

## Provenance and dependencies

The motivating source is Guy Henniart, *On the local Langlands conjecture for
GL(n): the cyclic case* (1986), Section 4.4, lemma and proof, printed page 159,
PDF page 16. Registered source: `henniart-1986-cyclic`; retained PDF:
`/home/taskhub/central-library/Henniart--On the Local Langlands Conjecture for GL(n) The Cyclic Case--1986.pdf`;
SHA-256 `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`.
Worker 468 read and visually checked that page. The implemented divisibility
induction is an elementary algebraic realization of recovery from nonzero zeros
and poles. The general reciprocal-radius criterion is derived here, as in the
published statement rationale; it is not attributed as a separate printed
Henniart theorem.

The proof imports the immutable target and the published
`Langlands.Representation.RankinSelberg.RationalEvaluation` module, including its
actual `RationalReflection.subst` infrastructure. The published
`Langlands.RankinSelberg.reflectionRigidity` theorem was inspected: it addresses
two polynomials related by reciprocal reflection under a strict radius gap.
The four-polynomial separation target instead assumes separate noncancellation
conditions and supplies no such gap for its arbitrary polynomial inputs, so
that theorem does not directly apply. No replacement of the target by that
special case is used.

This module proves only the algebraic conjunction. Representation-theoretic
pole regions, actual factor adapters, global functional equations and any
correspondence theorem remain outside its scope. No target or imported
Lean/Markdown pair is modified. The proof uses no new axioms or proof holes.
