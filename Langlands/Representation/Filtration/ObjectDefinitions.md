# Actual object filtrations and composition factors with multiplicity

Author: Worker 14. This definition pair supplies finite composition-series
predicates needed to state the length bound and the equality of
Jordan–Hölder multisets in Bernstein–Zelevinsky 1977, sections 2.8-2.9.
It does not prove those representation-theoretic results or the
Jordan–Hölder theorem.

`ObjectRepFiltration A n` reuses `RepFunctorFiltration` from
`Filtration.Definitions`: the functor is constant with value A on the
one-object discrete category. A filtration therefore consists of n+1
actual invariant subspaces, with monotone inclusions, first term zero,
and last term all of A. The constructor `ofSubrepresentations` turns
any such ordinary chain into this data. Its subfunctor stability law
is proved because all maps of the constant functor are identities;
there is no extra naturality hypothesis on the input chain.

`subrepresentation` evaluates a step at the sole object. Its monotonicity
and endpoint lemmas follow directly from the existing filtration laws.
`gradedRepresentation` evaluates the existing actual successive-quotient
functor. The quotient takes the upper invariant submodule and divides by
the pullback of the lower submodule along its inclusion; monotonicity
makes this the usual successive quotient. `gradedProjection` is the
actual quotient surjection, and its surjectivity is proved by the
published quotient-projection law.

Over a field, `HasSimpleFactors` requires each actual graded representation
to be irreducible, including nonzeroness. Thus repeated steps cannot
appear in a composition series. `HasCompositionSeriesLength A n` asserts
existence of such a filtration with n factors.
`HasCompositionLengthAtMost A b` asserts existence of one with at most
b factors. A length-zero series is allowed and its endpoints force A
to be zero.

`HaveSameJordanHolderFactors A B` asserts existence of composition series
of A and B with the same finite number of factors and a permutation
matching every pair of corresponding factors through an actual
representation equivalence. Each occurrence is matched, so multiplicities
are retained. No quotient of arbitrary constituent labels or equality
of sets without multiplicity stands in for the source's multiset equality.
The carriers of A and B may belong to independent universes.

The elementary reflexivity lemma uses a supplied series and identity
equivalences; the symmetry lemma reverses the permutation and the
equivalences. These constructions do not prove independence of the choice
of series. That independence, transitivity through arbitrary series,
and comparison with Mathlib's group-algebra finite-length predicate
remain separate theorem obligations. No such theorem is an input to
these definitions.

## Source and provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), section 1.2, printed page 443 / PDF page 4; sections 1.10-1.11,
printed page 445 / PDF page 6; and sections 2.8-2.9, printed pages 447-448 /
PDF pages 8-9. Source ID: `bernstein-zelevinsky-1977-induced-i`;
original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
These original pages were read directly, including fresh extraction of
pages 4 and 6 on 2026-10-20.

Section 1.2 defines JH as the isomorphism classes of irreducible
subquotients and JH° as the irreducible factors in a finite
Jordan–Hölder series, counted with multiplicity. Section 1.11 describes
gluing through a finite filtration and matching quotients up to
permutation. The current existential-series presentation is a derived,
concrete encoding of those notions. It is designed for statements in which
the input representations have finite length, such as section 2.9.

The filtration constructors work for a commutative coefficient ring and a
monoid. The simple-factor predicates use a coefficient field. This broader
algebraic generality concerns only the intrinsic constructions; it does
not assert a broader version of BZ77's theorems, whose intended
applications retain smooth complex representations over p-adic groups.
