# The normalized geometric lemma for GL

This module states Bernstein–Zelevinsky's geometric lemma, section 2.12,
using the actual normalized induction, Jacquet, and intersection transport
functors in the Library. The aggregate
`Langlands.Geometric.PadicGeometricLemmaTheorem` is a proposition definition;
this module does not prove it.

## Setting and actual groups

Fix a prime `p`, an actual finite extension `F : PadicField p` of the p-adic
field, its compatible `TopologicalData T`, a positive integer `n`, and ordered
positive block shapes `B C : BlockShape n`. Write `G = GL(n,F)`,
`M = B.Levi F.Carrier`, and `N = C.Levi F.Carrier`. All representations have
complex coefficients. The smooth categories use `T.topology` and the induced
product and subgroup topologies. No admissibility, irreducibility, or
finite-length hypothesis is imposed.

`MinimalRepresentatives B C` is the existing subtype of permutations `w`
which increase within every source block and whose inverses increase within
every target block. It is the concrete GL form of BZ's `W^{M,N}`. The existing
`WeylStatement` module separately states its parametrization of
`W_N \ W / W_M` and the corresponding parabolic double cosets `P \ G / Q`
by the inverse permutation matrix.

`IsIntersectionRefinement B C w S` abbreviates equality of all three existing
subgroups in `M`:

| Intersection subgroup | Standard refinement subgroup |
| --- | --- |
| `sourceParabolic F B C w`, or `M ∩ w⁻¹(Q)` | `refinedParabolic F B S` |
| `sourceLevi F B C w`, or `M ∩ w⁻¹(N)` | `refinedLevi F B S` |
| `sourceUnipotent F B C w`, or `M ∩ w⁻¹(V)` | `refinedUnipotent F B S` |

Here the intersections are represented by comaps along the actual matrix
conjugation and Levi embedding. The target triple is obtained by exchanging
`B` with `C` and replacing `w` by `w⁻¹`. A refinement gives an ordered positive
block shape in each block of its outer Levi. These are the same intersection
equalities already used in `PadicStandardIntersectionsTheorem`.

## Graded functors and filtration

`subgroupEqualityFunctor` relabels a smooth representation along equality of
its actual subgroup. Equality elimination makes it the identity functor.
It introduces no selected isomorphism or representation-theoretic hypothesis.
Its auxiliary construction works for any topological group.

For refinements `S` and `R` and the corresponding Levi equalities,
`geometricPieceFunctor T B C w S R hS hR` is the actual composite

1. normalized Jacquet from `M` to `refinedLevi F B S`;
2. equality relabeling to `M ∩ w⁻¹(N)`;
3. `intersectionTransportFunctor`, whose action on the target intersection
   is precomposition with inverse matrix conjugation;
4. equality relabeling to `refinedLevi F C R`;
5. normalized induction from this subgroup to `N`, followed by `SmoothRep.toRep`.

Thus this is BZ's `i_{N,N'} ∘ w ∘ r_{M',M}`, where
`M' = M ∩ w⁻¹(N)` and `N' = w(M) ∩ N`. The Jacquet functor uses the inverse
positive half of the product modulus; induction uses the positive half.
There is no additional character in the asserted graded piece.

`jacquetInductionFunctor T B C` is the actual composite
`T.normalizedParabolicInductionFunctor B ⋙ T.normalizedJacquetFunctor C ⋙
SmoothRep.toRep`. Both it and the graded functors have source
`SmoothRep.{0,uF,uV} ℂ M` and target `Rep.{max uF uV} ℂ N`, with independent
field and carrier universes. Jacquet and transport retain the input carrier
universe, while induction enlarges it to `max uF uV`.

`GeometricLemmaTheorem T B C` asserts existence of:

- one source and target standard refinement for every minimal permutation;
- proofs of all three subgroup equalities on each side;
- a finite enumeration of every minimal permutation, each exactly once;
- an `IsGluedFrom` relation between the actual composite and these graded
  functors.

The refinements and equalities precede the filtration in the existential
quantifiers. Their existence, and the filtration's existence, are conclusions.
They are not theorem-truth inputs. The Levi components of the equality witnesses
are used only to type the actual composite functors.

The imported `IsGluedFrom` means that, after a permutation of the finite list,
there is a filtration by actual natural subfunctors, starting at zero and ending
at the whole composite, with a natural isomorphism from each successive quotient
functor to its specified graded functor. The enumeration and filtration are
chosen once for the entire source category. Repeated zero graded pieces are
permitted. Forgetting to `Rep` retains all intertwiners and naturality; the
subrepresentations and quotients of the smooth values are the usual smooth
subquotients. The assertion is a filtration, not a splitting.

`PadicGeometricLemmaTheorem` universally quantifies this statement over the
prime, actual finite p-adic extension, compatible topology, positive rank,
and both block shapes. It does not assert a geometric lemma for arbitrary
topological groups or for positive-characteristic local fields.

## Source correspondence and provenance

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I*, Annales scientifiques de l'École Normale Supérieure
(4) 10 (1977), 441–472, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 2.12, printed page 448 (PDF page 9), states the functorial gluing and
explicitly describes one enumeration with natural filtrations and quotient
isomorphisms. Sections 2.11(b) and 6.3, printed pages 448 and 468 (PDF pages 9
and 29), supply the standard intersection Levis and the full parabolic triples.
Section 6.4, printed pages 468–469 (PDF pages 29–30), fixes the inverse
representative `P w⁻¹` and removes the possible extra positive character.
Sections 1.8 and 2.3 fix the normalized induction and Jacquet conventions.

This is the GL specialization of those statements. Bundling the simultaneous
refinements with the filtration combines 2.12 with its standardness prerequisite;
the equality-relabeling helper and the explicit composite are internal
constructions needed to express that specialization. The statement reuses
`RefinementFunctors`, `IntersectionTransport`, and `Filtration.Definitions`;
it introduces no arbitrary functor parameters or new axioms.

The induction constructors are the Library's smooth induced function spaces.
For the parabolics here, BZ 2.3 uses compactness modulo the parabolic to identify
them with compact induction. This module states the resulting lemma for those
actual smooth induction functors; it does not supply the compactness,
Haar-modulus identification, standardness, or geometric-lemma proofs. The
general orbit theorem of BZ 5.2, with arbitrary triples and characters, is
outside this statement's scope.
