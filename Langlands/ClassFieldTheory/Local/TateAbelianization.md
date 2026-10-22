# Local degree-minus-two cup and the Galois abelianization

Author: Worker 42.

Let `L/K` be a finite field extension. `integralTateMinusTwoEquiv K L`
identifies actual integral Tate cohomology in degree minus two with the
additive group underlying `Abelianization Gal(L/K)`. It specializes
`Langlands.Tate.integralMinusTwoEquiv`, which composes Mathlib's
Tate-to-first-homology comparison, its first-homology tensor-product
identification for trivial coefficients, and the explicit removal of the
lifted integer tensor factor. The local specialization uses the same
`Fintype.ofFinite` enumeration as the local Tate groups.

`integralTateMinusTwoEquiv_class` specializes the generic representative
certificate: the first-homology class of the single chain at an
automorphism, with coefficient one, maps to the abelianization class of that
automorphism. This comparison needs finiteness, but not Galoisness.

Now assume `L/K` is Galois. For any ordinary relative degree-two class `c`,
`abelianizationCupToNormQuotient K L c` is the additive homomorphism

`Gal(L/K)^ab → Kˣ / N(Lˣ)`

obtained by the inverse source comparison, left cup product with `c`,
and the existing Tate-zero/field-norm-quotient comparison. The norm subgroup
is the image of the actual determinant norm on units. No cohomology group
or quotient is replaced. The comparison certificate says that precomposing
this map with `integralTateMinusTwoEquiv` recovers
`negativeTwoCupToNormQuotient`.

The theorem `abelianizationCupToNormQuotient_bijective_iff` proves that this
map is bijective exactly when `relativeTateCup K L (-2) c` is bijective.
Its proof composes with the source equivalence in either direction and
uses the previously proved target-comparison certificate. Thus the
published all-integer predicate `FundamentalClassTateIsomorphisms` supplies
the needed condition when applied at minus two to a fundamental class;
the present file does not prove that predicate.

`abelianizationCupEquiv K L c h` turns the constructed map into a
multiplicative equivalence using an explicit proof `h` of cup bijectivity.
`abelianizationCupEquiv_apply` certifies that its forward map is the
constructed additive cup map, expressed in multiplicative notation.
`arithmeticReciprocityOfCup K L c h` takes its inverse equivalence. The
certificate `cup_arithmeticReciprocityOfCup` says that this inverse is
indeed inverse to the actual additive cup map. Finally,
`geometricReciprocityOfCup` postcomposes the arithmetic construction with
inversion in the abelianized Galois group, and
`geometricReciprocityOfCup_eq_inv` records that formula.

These are conditional constructors downstream of bijectivity. Their
names describe the convention for a class `c` whose invariant is
`+1/[L:K]`; they make no normalization assertion for an arbitrary class.
They assume neither an invariant map nor a class-formation record.
They do not assert the existence of a fundamental class or prove its
cup bijectivity. In particular, no choice of an unconditional local
reciprocity map is made. There is no topology on these equivalences and no
comparison with the separate topological or Weil reciprocity candidates.
Restriction, corestriction, inflation and the explicit cocycle sum formula
remain separate statements.

The base field and upper field have independent carrier universes `v` and
`u`. The coefficient ring is the actual lifted integer ring
`IntegerScalars.{u}`. All finite Galois extensions of every p-adic field
are covered by specialization; no Type-0 restriction is introduced.

Source: Serre, *Local Fields* (1979), Chapter XI, section 3, Theorem 1 and
the degree-minus-two special case, printed pp. 168–169 (PDF pp. 174–175).
The source puts the fundamental class of invariant `+1/[L:K]` on the left,
identifies the resulting degree-minus-two map with
`G^ab → Kˣ/N(Lˣ)`, and calls its inverse the reciprocity isomorphism.
The geometric convention used by the host project additionally inverts
the output of that arithmetic isomorphism. This extra output inversion
is distinct from taking the inverse of the cup equivalence.

This is derived content: the source and target comparisons and cup
operation are imported constructions, and the new comparison and
bijectivity certificates use equivalence inverse laws and composition.
The source representative certificate is a direct specialization of
the generic one. The conditional inverse uses `AddEquiv.ofBijective`;
the arithmetic and geometric certificates follow from its inverse laws
and the definition of output inversion.

Source ID: `serre-1979-local-fields`. Retained PDF SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
