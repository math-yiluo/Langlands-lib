# Actual real-twist families and opposite Jacquet occurrence loci

Author: Worker 167.

This internal definition unit packages the published actual induction, determinant
twist, inverse-conjugation transport, and opposite Jacquet class-exponent predicate.
It introduces no continuation hypothesis, selected irreducible quotient, or new
induction, conjugation, or Jacquet carrier.

The inducing carrier has universe `uV`, the candidate carrier has independent
universe `uW`, and the field has universe `uF`. The induced family has carrier
universe `max uF uV`. All real determinant parameters are retained, including
central directions and the one-block case. No positivity, irreducibility,
admissibility, temperedness, tensor factorization, or support is needed to define
the families.

All names below are in `Langlands.RealTwistFamilies`. The field is the actual
`PadicField p` with compatible `TopologicalData T`; `B`, `D`, and `C` are
ordered block shapes of the same ambient rank. Neither `D` nor `C` is required
to refine `B` in the general construction. The nested specialization adds an
actual `BlockRefinement B`. Rank zero is also allowed by these definitions.

## Induced and transported families

`induced T B σ t` is the existing upper normalized induction of
`T.leviRealPowerTwist B t σ.ρ`, bundled through
`CuspidalJacquetMultiplicity.induced`. Its character is

\[
\chi_{B,t}((m_i)_i)=\prod_i|\det(m_i)|_F^{t_i}.
\]

The absolute value is the published residue-normalized one. Determinant
exponents are `t i`; on the block scalars `a_i I_(B.size i)` they have weights
`(B.size i : ℝ) * t i`, by the imported
`T.coe_leviRealPowerCharacter_blockScalar`. No zero-sum constraint removes the
central direction, and no tensor factorization of `σ` is chosen.

`induced_apply` and `induced_representation` identify the bundle and its action.
`inducedEval` evaluates its actual smooth induced functions.
`inducedEval_action` proves right translation, `f(x g)`, and
`inducedEval_covariant` exposes

\[
 f(p x)=\delta_B(m(p))^{1/2}
       \chi_{B,t}(m(p))\,\sigma(m(p))f(x).
\]

The half modulus is exactly the existing positive square root of the upper
full block modulus. `induced_zero` recovers the existing induction of `σ`.
The smooth-function carrier may depend on `t`; no common model or analytic
trivialization of these carriers is supplied.

`transported T B D C w hw ω a t` twists `ω`
by the actual Mathlib affine map `a t` before applying the existing
`CuspidalSupport.transport D C w hw`. The proof `hw` says that the actual
permutation matrix of `w` conjugates the entire embedded `D`-Levi onto the
`C`-Levi. This hypothesis is geometric, with no occurrence content.
Writing `e = CuspidalSupport.leviConjugation D C w hw`, the action is

\[
 m\cdot v=\chi_{D,a(t)}(e^{-1}m)\,\omega(e^{-1}m)v.
\]

`transported_apply` and `transported_action` prove these identifications.
The carrier is precisely the carrier of `ω`, in universe `uW`.
Mathlib's `AffineMap` is reused without a new affine-data structure:
`affine_apply` proves `a t = a 0 + a.linear t`, displaying its offset and
real linear part. Such an affine map contains no occurrence or continuation
assumption. `AffineMap.const ℝ _ b + L.toAffineMap` gives the map `b + L t`.

`transported_zero` handles the zero affine map and leaves the ordinary Weyl
transport of `ω`. `conjugatesLevi_one` proves the identity conjugacy;
`transported_one` removes transport by that permutation for any affine map.
`transported_id` specializes both permutation and parameter map to identities.

## Occurrence and the nested parameter

`Occurs` applies `T.IsOppositeJacquetClassExponent C` to those two actual
representations at the same parameter. `occurrenceLocus` is its set of parameters.
`mem_occurrenceLocus` is the defining membership equivalence.
`occurs_iff` exposes precisely irreducibility, admissibility, and an actual invariant
subspace of the opposite Jacquet module with a surjective intertwiner to the
candidate. Admissibility uses `T.topology` and includes smoothness. It is a
condition on the candidate at the given parameter, not an input to its
construction. The source is the entire induced representation.

The opposite Jacquet bundle is exactly
`CuspidalJacquetMultiplicity.oppositeJacquet T C`: coinvariants under the
actual lower block radical, with normalization by the inverse of the upper
full modulus, hence the positive upper half-modulus in its action. There is no
replacement Jacquet carrier, formal character set, asymptotic module, or
certificate containing an occurrence conclusion.

`restrictParameter` uses the parent index from `B.flattenBlockEquiv S`.
`nestedParameter` is the affine map `-v₀ + restrictParameter B S t`.
`fineTwist_eq_nestedParameter` identifies its pullback along the existing
`flattenedLeviEquiv` with the published `RelativeJacquetMultiplicity.fineTwist`.
No scalar-root or refinement convention changes.
`nestedParameter_apply` proves the coordinate formula and
`nestedParameter_zero` proves that its offset is `-v₀`. These formulas apply
to every real `v₀`; they assert none of the support or positive-root hypotheses
required by the separate regular comparison target.

## Provenance, intrinsic proofs, and limits

This is internal packaging of the imported Library operations, not a theorem
stated in this form in the literature. The intended consumers are the separate
parameter-comparison, supported regular-comparison and quotient-extraction
tasks. Existing targets and their support hypotheses are unchanged.

The original is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. 236 (1978), 95–104, retained at
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
Printed p.96 supplies the normalized induction, the twist
`χ_ν(m) = q^(i⟨ν,H(m)⟩)`, and inverse-conjugation convention. Thus the real
determinant vector `t` corresponds to the source subscript `-i t`.
Printed p.97 defines class exponents by subquotients of the opposite Jacquet
module with the positive upper half normalization. We reuse the Library's
actual representative-based predicate; no equivalence with a new analytic
definition is asserted. The nested setup on p.99 uses `i(v₀-v'')`, hence
the determinant coordinates `-v₀ + restricted t` here.

The continuation passages in Lemma 5.6 (p.101), Proposition 5.8 (p.102), and
the proof of Proposition 6.1 (pp.102–103) motivate later consumers but are
not proved or encoded in this pair. Printed pp.96–97, 99, and 101–103 were
read directly in extracted text and page images; PDF page is printed page
minus 94. The source fingerprint was checked.
Registered source:
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.

This locus alone supplies no topology, analytic structure, continuation,
collision persistence, multiplicity constancy, or parameter-independent finite
Weyl branches. Occurrence in the entire induction is distinct from extraction
from an arbitrary given irreducible outer quotient. The published Lemma 5.3
[scope audit](../../../notes/jacquet/silberger-lemma53-scope.md) remains in force;
it is neither an author erratum nor a Lean theorem. Unrestricted Lemma 5.3 and
Corollary 5.4 are not used. The bare locus definition supplies no regularity
property of this subset of the real parameter space, and no extension from
generic to regular parameters. No parameterized head or irreducible quotient
is selected, and no downstream Langlands uniqueness is used.

The evaluation, action, membership, occurrence-unfolding and nested pullback
equalities are definitional. Covariance applies the existing normalized
induction covariance theorem to the actual twisted action. Zero identities use
the published zero-twist law. Identity transport uses injectivity of the Levi
embedding and the published inverse-conjugation embedding formula.
The affine formula follows from `AffineMap.map_vadd` at zero; the remaining
parameter equalities are pointwise arithmetic. These intrinsic proofs assert
no representation-theoretic continuation or classification result.
