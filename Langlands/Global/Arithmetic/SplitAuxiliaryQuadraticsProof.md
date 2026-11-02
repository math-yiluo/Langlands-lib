# Split auxiliary quadratic fields

`Langlands.Global.splitAuxiliaryQuadratics.{u}` proves exactly the existing
`Langlands.Global.SplitAuxiliaryQuadraticsStatement.{u}` in
`Langlands.Global.Arithmetic.FieldRealizationStatement`. It has no additional
outer hypotheses. For every rational prime `p` and totally real number field
`K : Type u`, it supplies actual rational intermediate fields `I,R` in
`AlgebraicClosure K`, both of degree two. The field `I` is totally complex,
and `R` is totally real. They are linearly disjoint, their compositum is
linearly disjoint from the supplied `K`, and each satisfies the existing
`HasSplitQuadraticPrime p` predicate. The arbitrary universe and every prime,
including `2`, are retained.

The Lean proof applies the published
`splitAuxiliaryQuadratics_of_prerequisites` to the two published theorems
`padicSquareNonsquare` and `quadraticPadicSplitting`. Thus both arithmetic
inputs of that conditional assembly are discharged. The implementation
described below is in those imported modules and their quadratic-root support;
the present module performs their final composition.

## Signed square classes and the common ambient fields

The signed-supply theorem works for any number field. For either sign, only
finitely many signed rational primes can become squares in that number field:
their generated quadratic intermediate fields are distinct, and a number field
has finitely many intermediate fields. Dirichlet's theorem supplies a prime
outside this finite obstruction in the residue class `1` or `-1` modulo
`4*p`. With the chosen sign, the resulting integer is congruent to `1`
modulo `4*p`. Hensel's lemma at `1` for `X²-d` applies because
`‖1-d‖ ≤ ‖2‖² * ‖p‖ < ‖2‖²`. At `p = 2` this uses modulus `8`;
it does not require that `2` be a unit in the p-adic integers.

The assembly works in `C = AlgebraicClosure K`. Let `B` be the actual image
of the canonical embedding of `K` in `C`, regarded as a rational intermediate
field. The canonical rational algebra equivalence `K ≃ₐ[ℚ] B` makes `B` a
number field. Apply the signed supply to `B`, obtaining a positive rational
`d` which is a square in `Padic p` and a nonsquare in `B`. Choose `x` in
`C` with `x² = d`, and set `R = ℚ⟮x⟯`.

Apply the supply again to the number field `M = B ⊔ R`, obtaining a negative
rational `a` which is a square in `Padic p` and a nonsquare in `M`. Choose
`y` in the same `C` with `y² = a`, and set `I = ℚ⟮y⟯`. The root-support
module identifies the square-root minimal polynomials and proves both
rational degrees are two. Under every complex embedding the positive root
has real image, which proves total reality of `R`. A real embedding of `I`
would give a negative real square, so `I` is totally complex.

## Both linear-disjointness assertions

Nonsquareness in `B` and then in `M` proves the actual degree equations

```text
[B ⊔ R : ℚ] = 2 * [B : ℚ],
[(B ⊔ R) ⊔ I : ℚ] = 4 * [B : ℚ].
```

Compositum dimension upper bounds and positivity of `[B:ℚ]` force
`[I ⊔ R : ℚ] = 4`. The dimension criterion for linear disjointness proves
`I.LinearDisjoint R` and `(I ⊔ R).LinearDisjoint B`. Invariance under the
canonical rational algebra equivalence transports the latter assertion to
`(I ⊔ R).LinearDisjoint K`, with the given scalar-tower embedding of `K`
in `C`. Thus both assertions concern the actual fields in the target's
common algebraic closure. The stronger signed supply makes total reality of
the input unnecessary for this degree argument; the theorem retains the
existing target's stated inputs.

## Actual primes and topological completions

For each of `I,R`, local squareness gives the two roots `z,-z` in
`Padic p`. The root-support theorem lifts them to distinct rational algebra
embeddings of the quadratic field. The proved `quadraticPadicSplitting`
then gives the full `HasSplitQuadraticPrime` conclusion.

That local proof identifies the quadratic tensor product over the rational
completion with the product of two copies of that completion. The published
canonical completed tensor comparison transports its nontrivial idempotent
to the product indexed by actual height-one primes over the rational place.
Two coordinates give distinct actual primes. Each local degree is positive,
and their sum is at most two. Consequently both selected degrees are one,
and there is no third prime over the rational place.

The rational-prime comparison proves that lying over this place is equivalent
to containing the image of `p` in the actual ring of integers. Each
degree-one canonical completion map is bijective and continuous; its inverse
is continuous by the finite-dimensional linear-map continuity theorem for the
existing completion topology. Composing its inverse with Mathlib's rational
completion equivalence gives a ring equivalence from each actual adic
completion to `Padic p`, continuous in both directions. Membership, exhaustion,
and all four continuity clauses are therefore supplied for each of `I,R`.
The target does not prescribe agreement of these completion equivalences with
the initially constructed global embeddings.

## Source correspondence and authorship

The motivating original is Guy Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique*, Inventiones Mathematicae 139
(2000), Section 3.3, printed page 449, second paragraph (PDF page 11).
Worker 27 read that page of the registered original
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
retained at
`/home/taskhub/central-library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
The paragraph chooses an imaginary and a real quadratic field split at `p`,
whose compositum is linearly disjoint from the previously chosen totally real
field. The common-algebraic-closure formulation, generic signed supply, degree
argument and explicit prime/completion comparisons are the project's derived
implementation of that choice, rather than assertions quoted verbatim from
the source.

Worker 27 authored the root support, conditional assembly and final composition.
Worker 384 proved the signed rational supply. Worker 1199 proved the actual
local splitting implication, with the rational-prime helpers contributed by
Worker 60. Their published modules are imported by Lean name. The statement
and its import closure are unchanged. This theorem supplies the auxiliary
quadratic component; totally real Galois realization and the later CM and
paired-place constructions remain separate results.
