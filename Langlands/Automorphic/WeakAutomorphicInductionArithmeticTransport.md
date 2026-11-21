# Arithmetic pullback of weak monomial automorphic induction

`Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.arithmeticComap`
transports an existing weak induction of a Hecke character. Let `L/K` and
`L'/K'` be extensions of number fields, with a commuting square of field
isomorphisms `e : K ≃+* K'` and `f : L ≃+* L'`. If a cuspidal class over `K'`
is weakly induced from `χ` over `L'`, its arithmetic pullback along `e` is
weakly induced from `HeckeCharacter.comap f χ`. The four field universes are
independent, and the two spectral presentations use the same arbitrary
carrier universe. The compactness instances are those used to form the
cuspidal classes. This does not assert existence of an induction or require a
Galois or cyclic extension.

## Proof

- For a finite place `v` of `K'`, use `Harris.finitePlaceEquiv_liesOver` for
  `(e, f)` and their inverses. This gives a bijection from the places of `L'`
  over `v` to the places of `L` over `finitePlaceEquiv e v`.
- The maps of integer rings take corresponding prime ideals to each other.
  The induced quotient-ring isomorphisms commute with the residue-field
  algebra maps: on a quotient representative this is the original commuting
  square restricted to integers. Invariance of the residue-field dimension
  preserves the inertia degree. Invariance of ideal multiplicity under the
  multiplicative equivalence of ideals preserves the ramification index, using
  the commuting square to compare the extensions of the downstairs ideals.
- `finiteCompletionEquiv f` preserves the valuation, so it sends any chosen
  family of uniformizers over the pulled-back place to a family over `v`.
  `HeckeCharacter.comap_finiteComponent` identifies the character values on
  these units, and `isUnramifiedAt_comap_iff` preserves character
  unramifiedness. Reindexing the product of the Euler factors preserves the
  induced polynomial, factor by factor, since the inertia degrees agree.
- Start with the attached spectral system witnessing weak induction over
  `K'`. Use `cuspidalArithmeticSpectralTransport` to get an attached system of
  the pullback, with equality of Euler polynomials at cofinally many
  corresponding good places (all but finitely many). Pull the cofinite
  weak-induction condition and the complement of the source exceptional set
  back along `(finitePlaceEquiv e).symm`. On the intersection with the cofinite
  transport condition, the source weak Euler identity gives the target one
  for every target uniformizer family. The degree equality in the rank
  condition follows separately from the commuting field isomorphisms.

## Provenance

This is a derived transport lemma for the Library's Euler-polynomial
formulation of Harris (1998), *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Definition 1.3(b) with inducing rank one (registered
source `harris-1998-local-langlands`). It supplies the weak-induction step in
transporting the constituents in the prime orbit of Proposition 4.8, printed
p.203 (`math_9611226v1.tex`, lines 1646–1655), and works also for the child and
CM comparisons where the types of the number fields need not coincide. The
proof uses the published cofinite spectral transport, not exact equality of
spectral presentations or any strong multiplicity-one assertion.
