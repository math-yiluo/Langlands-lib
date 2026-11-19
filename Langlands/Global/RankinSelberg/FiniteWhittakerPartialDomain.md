# Paired Whittaker products on the partial adelic domain

This internal unit shows that the paired Whittaker product of the actual
prescribed tensor vectors depends only on the infinite and `S` coordinates on
the domain of the partial Rankin–Selberg integral. Its provenance is actual
finite tensor covariance, the existing global Whittaker transformation laws,
and Worker 394's published group decomposition of that domain.

The entry is
`Langlands.Global.RankinSelbergGlobal.FiniteWhittakerPartialDomain.PartialDomainPairReductionStatement`;
`partialDomainPairReduction` proves it. Take a number field `F` with
`AdeleQuotient F` compact. Let `T`, `T'` be actual cuspidal realizations of
the same rank `r + 1`, with supplied spectral presentations whose actual
finite local components are irreducible and admissible. Let `S` contain both
exceptional sets. Choose arbitrary finite tuples `a`, `a'` at `S` and
arbitrary vectors `t`, `t'` of the tensors of the actual infinite source
models. Write `X = P.allPlaceTensorEquiv (P.finitePure a ⊗ₜ t)` and similarly
`X'` for the other presentation.

Let `ψ` be a standard adelic additive character in the published sense:
continuous, nontrivial, trivial on the number field and of modulus one. The
second Whittaker function uses exactly `ψ⁻¹`. For every actual adelic point
`g ∈ unipotentIntegralOutside F (r+1) S`, the statement is

`W_X(g) * W'_X'(g) = W_X(retainedPoint S g) * W'_X'(retainedPoint S g)`.

`retainedPoint S g` is the point with precisely the infinite and `S`-local
matrix components of `g` and identity components at every other finite place.
It is defined with the actual topological group equivalence `UnipotentClass.adelicSplit`.
The condition on `g` is the Library's actual `N(F_v) GL_(r+1)(O_v)` condition
at every place outside `S`, not entrywise integrality of `g`. Both universe
parameters remain free, and the case `r = 0` and empty `S` are included.

The proof removes the two extra factors in the group's decomposition.

1. `finitePure_fixed_away` proves that the exact restricted finite tensor is
   fixed by every finite adelic `d` whose `S` projections are identity and
   whose other projections are integral. The existing same-stage tensor
   action formula applies because the reference vectors outside `S` are
   fixed by those integral components. The action on every coordinate in
   `S` is identity. `fullVector_fixed_away` transports this equality through
   the actual full carrier tensor equivalence using its finite covariance.
   This argument treats the combined integral subgroup directly; it does not
   infer combined fixedness from fixedness at one place at a time.
2. `awayFinite k` uses `splitAtPlaces` to insert a supplied element of the
   away integral subgroup, with identity coordinates at `S`. The two local
   projection lemmas prove exactly its identity and integrality properties.
   `adelicSplit_away` identifies the corresponding point of Worker 394's
   coordinate decomposition with its finite adelic inclusion under the
   published adelic group-point equivalence.
3. `whittaker_mul_away` applies the genuine finite translation identity of the
   global Whittaker coefficient to the fixed global vector from step 1.
   Thus right multiplication of its argument by this away point leaves
   the Whittaker value unchanged, for any additive character.
4. `whittaker_pair_unipotent` applies the existing left-unipotent Whittaker
   identities to `ψ` and `ψ⁻¹`. Their character factors are reciprocals by
   `genericCharacter_inv`. Modulus one proves the first is nonzero, and
   cancellation gives invariance of the product. This step needs no tensor
   construction and applies to arbitrary two global vectors.
5. The published
   `exists_unipotent_mul_mul_of_mem_unipotentIntegralOutside` writes the
   original `g` as `n * retainedPoint S g * k`, with `n` adelic unipotent and
   `k` of the away integral form. The internal subtype wrapper
   `retainedPoint_decomposition` records the same equality with the two
   factors already bundled. Apply step 4 to remove `n`, and step 3 to each
   Whittaker factor to remove `k`. This proves exactly the displayed product
   equality.

The proofs do not separately claim invariance of either individual Whittaker
function under arbitrary adelic left unipotents: their opposite character
factors cancel only in the paired product. There is no conductor or finite
additive-support assumption outside `S`, since this cancellation is exact.
The equality also does not separate the remaining infinite variables into
individual place factors, assert a nonzero normalization constant, compare
ordinary and dual normalizations, or prove nonvanishing of an integral.
Those are further obligations of `ArchimedeanFactorizationStatement`.

`FiniteWhittakerSemilocalProduct` applies this equality before separating the
coordinates of `retainedPoint S g` into the finite product and the joint
infinite residual.
