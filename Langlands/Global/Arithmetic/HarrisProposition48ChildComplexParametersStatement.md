# The induced infinity type of an actual one-place child

The general-position prime branch supplies raw children whose weak
induction is witnessed at almost all finite places. It also supplies their
regular algebraic determinant twists. The complex-place parameters of the
raw children are needed for the parent's infinity type. This pair specifies
how to recover them for the actual raw representation, at its inherited
parity.

`IsobaricHeckeComplexPlaceParameterTCStatement` is the totally complex
version of `IsobaricHeckeComplexPlaceParameterStatement`. In the proof of
that endpoint statement, realize each Hecke character on the actual cuspidal
`GL(1)` character line by the determinant multiple of the trivial line.
Its spherical Euler polynomial at a good place has one factor. Its
complex parameter in the selected coordinates is the character's actual
infinite component. Compare the finite family of these classes with the
endpoint by Euler constituent recovery at the top field. This recovers the
actual multiset, including multiplicities, so complex parameters match up
to the permutation allowed in both predicates. The TC premise applies at
that field. This is the same endpoint argument specialized to the fields
used here.

`Proposition48AuxiliaryChildComplexParametersStatement` uses this TC
endpoint, the TC cyclic isobaric base-change existence premise, the TC
complex-place compatibility premise and TC Euler constituent recovery.
Its input `S` is an actual cuspidal realization weakly inducing `R.ξ` with
unitary central character. The auxiliary place data give the following
route.

1. The closure `R.L/R.E` is finite Galois. Its Galois group is identified
   with the Galois group of the completion at the unique place over
   `R.Ps.v`. Every automorphism preserves that place and extends to the
   completion. In the other direction normality ensures that an
   automorphism over the base completion carries the embedded global
   normal closure to itself, and density identifies the extensions.
   `R.Ps.IsCompatible` gives the commuting isomorphisms to `R.F` and its
   local normal closure. Transfer the local cyclic prime tower from
   `harrisCyclicPrimeTower`, reverse it and use the corresponding global
   fixed fields. Every level is totally complex by the finite extension
   of the CM base.
2. Begin at the singleton of `S.isoClass`. Construct the unitary isobaric
   datum at each next level by `CyclicPrimeIsobaricBaseChangeTCStatement`.
   The relation between adjacent levels has actual spectral attachments.
   The rank is preserved. Along the tower the exponent in the Frobenius
   eigenvalue operation multiplies, since the residue degrees multiply.
   Pull back the finite exceptional sets and use cofinite equality of
   systems attached to the same multiset, from TC constituent rigidity
   and comparison of two presentations of each constituent.
3. Over `R.L`, form the Hecke characters obtained by the norm pullbacks of
   `R.ξ` from the conjugate copies of `R.E'`, one for each `R.E`-embedding
   of `R.E'` into `R.L`. This is the rank-one splitting of the induced
   parameter over a field containing the normal closure. At a good
   finite place, start with the product of factors
   `1 − χ_w(ϖ_w) X^f(w|v)` over all places `w` of `R.E'` above the base
   place `v`. On the top field, base change raises each eigenvalue to
   the top residue degree. The eigenvalues above a given `w` then each
   give the same power of `χ_w(ϖ_w)`, with `f(w|v)` occurrences. They
   agree with the corresponding norm-pulled characters of the top
   field. This is the unramified Euler calculation for
   `IsobaricData.HasHeckeFamily`, using the actual terminal attachment.
4. Over any chosen complex place of the top field, the embeddings of
   `R.E'` correspond to its complex places over the base place, with
   the choice of coordinate determined by the chosen top embedding.
   The rank-one character parameters are therefore the Langlands sum
   indexed by those places. Apply the TC Hecke-family endpoint to this
   list, then transport back down the tower by the unitary-isobaric clause
   of `CyclicWeakBaseChangeComplexPlaceTCStatement`. In complex
   completions every step uses the same identity/conjugation convention
   of `complexPlaceParameterTransport`, which composes along the tower.
   At the bottom `hasComplexPlaceParameter_ofCuspidal` obtains an actual
   cuspidal parameter witness, with the permutation of the induced list
   permitted by `IsInducedComplexPlaceParameter`.

The conclusion is the existing `R.HasInducedComplexPlaceParameters`.
It supplies parameter data of the child for subsequent arithmetic
transport. The parent's regular algebraicity still uses the induction in
stages and the archimedean bridge. The cyclic compatibility used on the
tower concerns complex places. The supercuspidal comparison at the split
finite place is a separate input of the original prime branch.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), `harris-1998-local-langlands`,
  Definition 1.3(b), p. 186, Lemma 1.6, pp. 188–189, Proposition 2.4,
  p. 194 and formula (2.4.2), and Proposition 4.8, pp. 202–203. The
  displayed complex Langlands sum is the desired infinity type. Harris
  proves the monomial induction statement by comparing Mackey
  constituents along the prime tower. The recovery for a supplied child
  here is a derived application of base change to that situation.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula* (1989), `arthur-clozel-1989-base-change`,
  Chapter III, Theorem 4.2(c), pp. 202–203, for the isobaric chain, and
  Theorem 5.1, p. 212, including the split complex local comparison.
- J. Tate, *Number theoretic background*, Corvallis Part II (1979),
  `tate-1979-number-theoretic-background`, (2.3.5), p. 12. The formula
  is used with all places above the base place in the Euler calculation.
