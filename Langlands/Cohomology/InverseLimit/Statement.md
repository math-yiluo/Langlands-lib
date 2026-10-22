# Countable inverse limits and cohomology

`Langlands.Cohomology.InverseLimitComparisonStatements` is the conjunction of
five actual proposition definitions. It assumes none of their truth. The
underlying theorem and its proof have been read in the supplied EGA original;
no Lean proof or independent acceptance of this contribution is claimed.

`Langlands.Cohomology.MittagLefflerExactSequenceStatement` states the
Mittag-Leffler closure properties in a short exact sequence of module towers:
the condition passes from the middle tower to the quotient, and from both
outer towers to the middle one.

`Langlands.Cohomology.MittagLefflerShortExactLimitStatement` states that an
actual short exact sequence of towers remains short exact after applying
the inverse-limit functor if its kernel tower is Mittag-Leffler. Exactness
after the limit is the conclusion, not a functor property assumed in order
to construct the sequence.

`Langlands.Cohomology.DegreewiseInverseLimitCohomologyStatement` states that
degreewise Mittag-Leffler implies surjectivity of the canonical comparison in
every degree \(q\). If the cohomology tower in degree \(q-1\) also satisfies
Mittag-Leffler, the comparison in degree \(q\) is an isomorphism.

`Langlands.Cohomology.InverseLimitCohomologyStatement` asserts that the canonical
map from the cohomology of an inverse limit of cochain complexes to the inverse
limit of their cohomologies is an isomorphism, provided both the degreewise
module systems and the cohomology systems satisfy the Mittag-Leffler condition.

`Langlands.Cohomology.FiniteCohomologyInverseLimitStatement` records the sufficient
conditions used in Harris's application: the transition maps of the complex
are surjective in every degree and each cohomology group is finite. It asserts
invertibility of the same canonical comparison.

The three comparison declarations quantify over actual Mathlib cochain complexes of modules
and their chain maps, indexed by the opposite of the ordered natural numbers.
Their limit is Mathlib's categorical limit; its intrinsic complex and cone
identities are already proved in Mathlib. Cohomology is the kernel/image
construction of `HomologicalComplex.homologyFunctor`. The comparison is
`CategoryTheory.Limits.limit.post`, constructed by applying cohomology to the
limit projections and using the limit universal property. It is defined
without assuming preservation of this limit. Its invertibility occurs only
as a conclusion. The surjectivity conclusion uses the underlying function of
this same module morphism.

The coefficient ring and module carrier have independent universe parameters.
The ring is not assumed commutative, so the algebraic target also permits an
actual group ring. Complexes are indexed by the integers; no boundedness is
built into the statements. The tower's natural-number index starts at zero;
Harris's coefficient exponent starts at one and is reindexed by adding one.
All-arrow surjectivity in the fifth target is equivalent to consecutive
transition surjectivity for this index category, but that equivalence is not
assumed as a new theorem.

## Original-source correspondence

A. Grothendieck (with the collaboration of J. Dieudonné), *Éléments de géométrie
algébrique III, Première partie*, Chapter 0, Sections 13.1–13.2,
Publications Mathématiques de l'IHÉS 11 (1961), printed pp.64–67:

- Literature ID:
  `provided-bca66cf9ddf1864d04cd9ab13db3799e640164f5476bbe9ed23714ccc825ed03`.
- Registered folder SHA-256:
  `fb65e01feda254662655043bb84b343601696054c02f2c05f42548e66042f1d4`.
- Actual file:
  `literature/EGA III, first part (1961), original containing Chapter 0 §13.2/Grothendieck--Preliminaires (EGA III-1, Chapitre 0, sections 8-13)--1961.pdf`.
- PDF SHA-256:
  `24cb7a75e125f44022411d4b2a86afd2453ab45876945e0ee02b5dd8d5dc5655`.
- Definition 13.1.2, printed p.65 / continuous p.409, defines Mittag-Leffler
  by stabilization of transition images and records the surjective and
  Artinian sufficient conditions.
- Proposition 13.2.1, pp.65–66, gives closure properties in exact sequences.
- Proposition 13.2.2, p.66 / continuous p.410, gives exactness of inverse
  limits of short exact sequences when the kernel tower is Mittag-Leffler
  and the directed index set has a countable cofinal subset.
- Proposition 13.2.3 and equation (13.2.3.1), pp.66–67 / continuous
  pp.410–411 / PDF pp.62–63, give precisely the canonical comparison,
  surjectivity and preceding-cohomology criterion used here.

The supplied 75-page original is the preliminaries, printed pp.5–79, and
contains Chapter 0 Sections 8–13. It is not the complete fascicle pp.5–167.
Sections 13.1–13.3 and their proofs were read, and the statement and proof
of Proposition 13.2.3 were visually checked in the PDF.

The first two targets are the module versions of Propositions 13.2.1 and
13.2.2, with actual `ShortComplex` objects in the category of module towers,
and `ShortExact` meaning monomorphism, exactness in the middle and epimorphism.
The limit sequence is `S.map lim`: both maps are induced from the original
natural transformations. Short exactness in a functor category is pointwise
short exactness; no extra exactness of the limit functor is a hypothesis.

The degreewise comparison target specializes EGA's directed index set to the natural numbers.
Its unbounded integer grading and degree \(+1\) differential are exactly
the source's convention. The module-valued formulation is a derived extension:
limits, kernels and quotients are computed on underlying abelian groups with
their induced module operations; the canonical comparison is linear. The
source's bijectivity therefore gives an isomorphism of modules. This does
not require commutative coefficients. Mathlib's Mittag-Leffler predicate after
`forget` tests stabilization of the actual underlying images, which agrees
with the source's condition for module transition maps.

The fourth target assumes Mittag-Leffler in all cohomological degrees and
thus applies the preceding-degree criterion for every \(q\). For the fifth,
surjective transitions give the degreewise condition; a decreasing family of
subgroups of a finite group stabilizes, giving the cohomological condition.
Here `Finite` means a finite underlying set, not merely finite dimension or
finite generation. These implications explain the derived specializations;
their Lean proofs remain obligations.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), pp.299-318, Section 2, especially
Facts 1 bis and 2 on p.303, Lemmas 2.2 and 2.2 bis on pp.304-305,
equations (2.6)-(2.7) and Lemma 2.8 on p.306, supplies the intended geometric
application. The complete paper was read in the preceding audit and the
Section 2 argument was read again for these targets.

- Literature ID: `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
- Retained PDF SHA256:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- Retained original:
  `literature/Harris (1999), Galois properties of cohomological automorphic forms on GL(n).pdf`.

Harris explicitly invokes EGA III, Chapter 0, Proposition 13.2.3. The supplied
original resolves acquisition request `96dfdcea85445ba8b675d59631c76839`;
the operator response is already completed and immutable. The algebraic
propositions do not assert that any particular geometric tower satisfies
their hypotheses.

These are algebraic prerequisites, not substitutes for constructing Harris's
complexes or establishing their stated properties. The smooth group actions,
compact-support comparison, divisibility, and finite-dimensional geometric
vanishing still require their own actual definitions and statements.
In particular the hypotheses on the local prime, distinct coefficient prime,
analytic space, compact open subgroup and unitary Shimura data have not been
removed from the geometric theorem: that theorem has not yet been stated here.

## Dependencies and status

Only the pinned Mathlib environment is imported: environment artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. There is no project mathematical
dependency.

The registered statement target is the conjunction of the five declarations;
all component definitions remain separately named for later use. Proofs of the
comparison and of the two specializations are separate obligations.
Compilation and inspection do not establish these propositions.

Authored by Worker 3.
