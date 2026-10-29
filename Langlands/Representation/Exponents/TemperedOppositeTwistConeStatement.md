# Pointwise cone bound for an opposite Jacquet occurrence

This file defines the proposition
`Langlands.GLTemperedOppositeTwistConeStatement.{uF,uV,uM}`. It is a
Prop-valued definition. It states the assertion and does not prove it.

Worker 429 drafted the Lean statement after coordinating with Workers 359
and 349. Worker 264 compiled and inspected it and wrote this Markdown.

## The statement

The proposition quantifies over:

- every prime `p`, every p-adic field `F : PadicField.{uF} p` and all
  supplied compatible topological data `T`;
- every positive rank `n` and two standard block shapes `C, E` of `n`.
  One-block shapes are included;
- a coordinate permutation `w` together with the witness
  `hw : CuspidalSupport.ConjugatesLevi C E w`. This witness says that
  conjugation by the permutation matrix of `w` maps the embedded Levi of
  `C` onto the embedded Levi of `E`;
- a fine representation `ω : Rep.{uV} ℂ (C.Levi F)` that is irreducible,
  admissible and unitarizable;
- arbitrary real vectors `v, b : Fin C.length → ℝ`;
- a representation `A : Rep.{uM} ℂ (GL_n(F))` with `T.IsTempered A.ρ`.

The field, fine carrier and ambient carrier universes are independent.

The candidate is

```text
Rep.of (transport C E w hw
  (T.leviComplexPowerTwist C (fun k => -(v k) + I * b k) ω.ρ)).
```

So block `k` of `C` is twisted by the complex determinant power with
exponent `-v k + I b k`. The result is then transported to `E.Levi` along
the given conjugation. `transport` acts through the inverse conjugation,
as in Bernstein–Zelevinsky (1977), section 1.7.

The premise is `T.IsOppositeJacquetClassExponent E A candidate`. By its
Library definition (`Exponents/DualJacquetStatement.lean`), this means
three things:

- the candidate is irreducible;
- the candidate is admissible;
- some invariant subspace `U` of the normalized opposite Jacquet module
  `CuspidalJacquetMultiplicity.oppositeJacquet T E A` has a surjective
  intertwiner `U → candidate`.

This premise is not an embedding of `A`, not a quotient of the whole
Jacquet module, not a Hom-dimension bound and not a scalar-character
bound.

The conclusion is `Exponents.IsClosedPositiveRootCone V` for the
diagonal vector

```text
V(a) = v(blockIndex C (w.symm a)),   a : Fin n.
```

The same `w` appears in the transport and in the conclusion. Coordinate
`a` of the target therefore reads the source block containing
`w⁻¹ a`. `IsClosedPositiveRootCone` (in `Exponents/Chambers.lean`)
requires `∑_a V(a) = 0` and `partialSum V k ≥ 0` for every proper cut
`0 < k < n`. This includes cuts inside the blocks of `E`. Each exponent
`v k` is repeated on every coordinate of its block. The conclusion
therefore keeps the block-size weights. It is not a statement about
unweighted block exponents.

### Generality of the ambient source

The proposition places no premise on `A` beyond `T.IsTempered A.ρ`. In
particular there is no irreducibility, finite generation, finite length,
factorization or cuspidal-support premise. The Library predicate
`IsTempered` (`Classification/Tempered.lean`) asks, for every Haar
measure, for admissibility, a unitary central character and matrix
coefficients in `L^(2+ε)` modulo the centre. Admissibility and the
unitary central character therefore come from this predicate. They are
not extra premises.

The fine representation `ω` has no cuspidality or square-integrability
premise.

## Sign convention

The Library normalizes the opposite Jacquet action by the positive upper
half modulus. With this normalization, the opposite exponents of a
tempered representation have real parts in the closed *negative* cone.
As an informal check, for the Steinberg representation of `GL_2` they
are `(-1/2, 1/2)`. The candidate's real determinant exponent is `-v`, so
the conclusion is the positive cone for `v`. The imaginary parts `b` and
the unitary central character of `ω` contribute characters of absolute
value one. The statement asserts none of these scalar facts. They are
obligations of the later proof.

## Provenance

This is an internal, derived interface. It is not the wording of a
separately numbered theorem in the literature. It isolates one pointwise
step used in

- J. Silberger, *The Langlands quotient theorem for p-adic groups*,
  Math. Ann. 236 (1978). Registered source
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA256
  `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.

The page images were read: PDF page 5 is printed p.99 and PDF page 7 is
printed p.101.

- Printed p.99 sets up the support condition: the induced representation
  `I(P',ω')` is tempered, so every exponent `ω^s_{i s ν₀}` in
  `D_{I(P',ω')}(P,A)` satisfies `s ν₀ ∈ +a*`.
- Printed p.101, proof of Lemma 5.6: for almost all `ν'`, the exponent
  `ω_{sν' + i s ν₀}` lies in `D_{C^G_{M'}(ω'_{ν'})}(P,A)`. Temperedness
  of the relevant class then gives `s ν₀ ∈ +a*`.

The present proposition is the `GL_n` version of this pointwise
"tempered source, actual occurrence, cone" step. It uses Library
predicates in place of Silberger's exponent sets. The public notes
`notes/jacquet/silberger-continuation-parameters.md` and
`notes/jacquet/silberger-lemma53-scope.md` explain how the continuation
parameters and the scope of Lemma 5.3 are used.

The proposition is pointwise. It may be applied to a single parameter
taken from a full-measure set produced elsewhere, after that occurrence
has been obtained and the ambient source separately shown to be
tempered. It contains no almost-everywhere statement. In particular it
does not justify specializing an almost-everywhere occurrence to the
parameter zero.

## Boundaries and obligations of a proof

The proposition proves none of the following. A proof must supply them
or cite published results.

- **Scalar character.** The proof must construct the unitary central
  character of `ω` and compute the scalar character of its complex twist.
  It must then transport that character through the Levi conjugation.
  For the twist, the imported `Langlands.LeviComplexPowerConjugationStatement`
  (proved in the Library as `Langlands.leviComplexPowerConjugation`) says
  that transport reindexes the exponents by the block bijection
  `blockEquiv hw`. The real part of the resulting scalar exponent is
  `-v`, weighted by block size.
- **Necessity for a general source.** The proof needs a necessary
  scalar-character bound for an actual opposite Jacquet subquotient of a
  *general* tempered `A`. The existing statements
  `Langlands.GLDualJacquetFinitenessStatement` and
  `Langlands.GLOppositeJacquetSubquotientExponentInheritanceStatement`
  both assume that the ambient `A` is irreducible and admissible. They
  cannot be applied to a general `A` without further argument. Nor may
  one infer a global finite dual spectrum for every admissible source. A
  route through finite-dimensional compact-open fixed spaces may avoid
  that. Worker 84 suggested such a route, but it is unverified and is not
  a premise of this proposition.
- **Chamber.** `Langlands.GLTemperedExponentCriterionStatement` concerns
  *upper* Jacquet exponents and uses the chamber where
  `i ↦ normalizedAbs (a i)` is monotone. Passing from the opposite to the
  upper side, together with the Weyl and modulus identifications, is a
  separate obligation, as is the correct opposite chamber.
- **Interior cuts.** The witness `hw` should make `V` constant on each
  block of `E`; this must be proved from `hw`. Partial sums at interior
  cuts then interpolate linearly between the size-weighted sums at the
  adjacent block boundaries.

The proposition supplies no branch selection, continuation,
almost-everywhere occurrence, tempered induction, composition series,
multiplicity equality, quotient existence or irreducible head. Those
assertions belong to separate tasks.
