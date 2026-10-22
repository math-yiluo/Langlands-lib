# Cuspidal embedding and normalized induction for actual GL_n

Author: Worker 14. These proposition definitions specialize Bernstein and
Zelevinsky (1977), theorem 2.5 and theorems 2.8–2.9, to actual general linear
groups over finite extensions of p-adic fields. They assert no proofs and
assume no theorem truth as data.

The aggregate `PadicCuspidalInductionTheorems` quantifies every prime, every
actual finite p-adic extension, every compatible topological realization,
and every positive rank. The representation spaces are complex modules,
with independent universes for the two inducing representations. Smoothness
is encoded by the published `SmoothRep` category. The groups, block shapes,
Levi projections, characters, and invariant subspaces are actual constructions.

All inductions use the published smooth right-translation action on
covariant functions. The covariance representation is the Levi action
inflated through the actual upper-parabolic projection, then twisted by
`T.parabolicHalfModulus B`, the canonical positive complex half-modulus.
This is normalized upper induction, with no arbitrary normalizing character
supplied by the caller. The expressions reuse the existing induction and
block-modulus definitions directly. The induced function space has universe
`max uF uV`, so embeddings use actual intertwining maps, which permit
different source and target carrier universes.

- `CuspidalEmbeddingTheorem` states that every irreducible smooth GL_n
  representation is admissible and injects into normalized induction from
  some actual standard Levi and some irreducible cuspidal smooth representation
  of that Levi. The source and inducing carriers may both be taken in the
  given carrier universe: the inducing representation can be realized by
  subquotients of Jacquet modules of the source. Admissibility of the source
  is a conclusion. The chosen Levi need not be proper.
- `CuspidalInductionLengthTheorem` states finite length as a module over the
  actual complex group algebra. It also requires an actual composition series
  with at most `B.length!` irreducible factors, using the published
  `HasCompositionLengthAtMost` predicate. This retains the numerical bound
  from theorem 2.8, including multiplicities. No irreducibility of the induced
  representation is claimed.
- `CuspidalInductionAssociationTheorem` states the equivalence of association
  of the inducing representations with each of three conditions: an actual
  nonzero intertwiner between the inductions; matching composition factors
  with multiplicities; and a common irreducible subquotient. Association
  already includes permutation conjugacy of the actual embedded Levis.
  Factor matching uses `HaveSameJordanHolderFactors`, witnessed by actual
  finite series, a permutation, and equivalences of the corresponding graded
  representations. Common occurrence is witnessed by an invariant subspace
  and a quotient in each induced representation, an irreducibility assertion,
  and an actual equivalence of those two subquotients. Equivalence transfers
  irreducibility to the second. This formulation allows independent carrier
  universes without choosing one isomorphism-class universe.
- `CuspidalInductionHomBoundTheorem` states finite dimensionality of the actual
  complex intertwiner space and bounds its finrank by the finite subtype of
  minimal permutations associating the inducing data. Finite dimensionality
  is stated explicitly so that finrank cannot hide an infinite-dimensional
  space. Both inputs are irreducible and cuspidal.

## Original source and specialization

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), sections 2.1–2.9, printed pages 446–448 (PDF pages 7–9), and the
corollary and proofs in sections 2.13–2.15, printed page 449 (PDF page 10).
The original passages were read, including the retained page text on
2026-10-20. Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Theorem 2.5 is the embedding and admissibility assertion. Section 2.8 states
that its Weyl-coset bound l(M) is r! for a GL Levi with r blocks. Theorem
2.9(a) gives the four equivalent conditions; its JH^0 equality retains
multiplicities. Theorem 2.9(b) bounds the Hom dimension by
`W(rho,rho') / W_M`. Section 2.13(c) identifies the minimal conjugating
representatives with the right-coset set for associated Levis. Restricting
that representative set by an actual transport equivalence gives precisely
the count used here. The definition of this subtype does not itself prove
that identification; its proof remains a prerequisite of proving the bound.

Sections 2.1–2.3 set the smooth complex, normalized induction convention;
section 2.2 identifies GL standard Levis with positive ordered blocks.
Section 2.4 defines cuspidality as admissible quasicuspidality, retained by
`IsLeviCuspidal`. The general reductive assertions are restricted to GL_n
and to finite p-adic extensions. No general reductive tempered-induction
irreducibility assertion is introduced.

BZ77 refers to its reference [10], and [1] chapter II in the GL case, for
theorem 2.5. Those proof sources remain future proof-source obligations.
The proofs of 2.8 and 2.9 use the normalized geometric lemma, quasicuspidal
structure, and Jordan–Hölder theory. These are separate obligations;
compilation of the present proposition definitions establishes none of them.
