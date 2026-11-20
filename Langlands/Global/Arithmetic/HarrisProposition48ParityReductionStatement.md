# Reductions for the Proposition 4.8 parity obligations

These four conditional propositions conclude the four published
`Langlands.Global.Harris.Proposition48…Statement` targets for
auxiliary and full parity normalization and untwisting. The local
field and local representation carriers retain independent
universes `uF` and `uV`.

## Auxiliary normalization

`Proposition48AuxiliaryParityNormalizationReductionStatement` assumes
the infinity and CM norm transport, actual finite component transport,
and preservation of general position under an ambient Weil twist.

Let `d = [E' : E]` and `m = (b + (d − 1)) % 2`. If `b` and `d − 1`
have the same parity, take `ν = 1`. It is conjugate-inverse and has
the zero integral infinity type. If they differ, `m = 1`. Choose one
complex embedding `τ` of the imaginary quadratic subfield `K₀` of
`E`. Put exponent one on embeddings of `E` extending `τ`, and zero
on those extending its conjugate. The lemmas `eq_or_eq_conjugate`
and `conjugate_comp` in `HarrisDatumArchimedean` verify that the two
exponents of every conjugate pair add to one. Apply the published
`Langlands.Global.cmHalfWeightCharacter` with this pure weight-one
type and the empty finite set. Its infinity formula gives
`IsAlgebraicAfterTwist 1 ν`, and it gives conjugate inversion on
actual idele classes.

Use the norm pullback in `Q.correctedCharacter ν`. The infinity
input gives algebraicity after twist exponent `b + m`, which
has the parity of `d − 1`. Apply
`isAlgebraicAfterTwist_add_two_iff` to reduce both exponents to
their residues. The other infinity conclusion gives relative
regularity. Norm conjugation and the two conjugate-inverse
equations give conjugate inversion of the corrected character.
Use `Proposition48PlaceNormTwistStatement` at `Q.Ps` to obtain
the actual corrected component. Its ambient Weil character
transports general position with the original cyclic tower.
The field and place clauses follow from the original auxiliary datum.

## Two-place normalization

`Proposition48ParityNormalizationReductionStatement` projects the
full input to the auxiliary validity conditions. The auxiliary
normalization provides `ν` and the corrected component at `Q.Ps`.
Use the actual component transport again at `Q.P` with the same
`ν`. Reassemble full validity using the original primary place,
compatibility, uniqueness, and distinctness clauses. The auxiliary
route needs only the specified auxiliary completion identifications.

## Auxiliary untwist

`Proposition48AuxiliaryParityUntwistReductionStatement` assumes the
weak induction, conjugate self-duality, and supercuspidality twist
inputs. Choose an actual representative `T` of the supplied corrected
cuspidal class `c`, and take `S = T.heckeDeterminantTwist ν⁻¹`. This is
the existing arbitrary-character construction. The inverse of
`T.realization.heckeDeterminantTwistEquiv ν⁻¹` gives the required
linear equivalence from `S` to `T`. The evaluation formula for the
equivalence and cancellation of reciprocal multipliers give
`IsDeterminantMultiple ν S.realization T.realization`.

At `T`, use `isWeakAutomorphicInductionOf_iff` to obtain an actual
presentation. Twist it by `ν⁻¹` and cancel the norm-pullback factors
pointwise to give the weak induction of `Q.ξ` at `S`. The inverse of
a conjugate-inverse character is conjugate-inverse. The conjugate
self-duality input on `T.realization` therefore gives conjugate
self-duality on `S.realization`. Use `hasSupercuspidalComponent_iff`
at `T` for the presentation with a supercuspidal component at `Q.Ps.v`.
The supercuspidality input at that presentation gives the required
component at `S`. These two uses of presentation existence are
independent. The four corrected properties hold at `T` by
`T.isoClass = c`. The output assigns regular algebraicity to `T`.

## Two-place untwist

`Proposition48ParityUntwistReductionStatement` assumes just the
auxiliary untwist. Project full raw and corrected validity to
auxiliary validity. The `IsSolution` predicate on the corrected
datum depends on the corrected inducing character and auxiliary
place. Both untwist conclusions ask for the same `IsUntwistedSolution`
on the original `Q`, so the auxiliary conclusion supplies the full one.

## Provenance

The reductions implement the parity condition on printed p. 195 and
the induction in Harris's Proposition 4.8, pp. 201–203. The
half-integral absolute value twist in the remark on p. 191 concerns
fields of definition. The existence and conjugate inversion of the
odd correcting character use the Library construction based on
Harris–Taylor, Proposition VII.2.7, p. 238, and Corollary VII.2.8
and proof, pp. 244–245. The actual determinant multiplier follows
Henniart, §2.2, p. 444. The implications are derived from these
constructions and the exact Library targets.
[Harris 1998](https://arxiv.org/abs/math/9611226), [Harris–Taylor 2001](https://press.princeton.edu/books/paperback/9780691090924/the-geometry-and-cohomology-of-some-simple-shimura-varieties), [Henniart 2000](https://doi.org/10.1007/s002229900033)
