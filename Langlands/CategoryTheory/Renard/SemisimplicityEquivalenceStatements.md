# Renard A.VII: the semisimplicity equivalence

Module: `Langlands.CategoryTheory.Renard.SemisimplicityEquivalenceStatements`.
The single declaration
`Langlands.Renard.SemisimplicityEquivalenceStatement` is a definition returning
`Prop`. It states the lemma of A.VII and an internal size comparison for the
existing semisimple-object alias. This unit supplies no proof of those
equivalences.

## Original and conventions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The heading A.VII is at the end of printed264/PDF270. Its unnumbered lemma,
proof and following corollary are on printed265/PDF271. The lemma states that,
in an abelian category satisfying the preceding section's hypotheses, the
following three conditions on an object are equivalent:

1. It is isomorphic to a direct sum of simple objects.
2. It is the sum of all its simple subobjects.
3. Every subobject admits a complementary subobject, with their inclusion maps
   presenting the ambient object as their direct sum.

The preceding hypotheses are source Grothendieck and source AB6, introduced
on printed263/PDF269. Renard's Grothendieck condition is existence of arbitrary
direct sums together with the AB5 distributivity law for directed sums of
subobjects. It has no generator clause. Renard's AB6 is local finite type:
every object is the sum of its finite-type subobjects. The source footnote
distinguishes this from Grothendieck's Tohoku AB6. The imported public
`IsSourceGrothendieck` and `SourceAB6` retain these conventions.

Worker 6 read PDF269–271 in full and visually inspected PDF271; Worker 1069
independently reread PDF269–271 from the file with the SHA256 above. The
published `notes/renard/appendix-a-corrections.md` concerns other passages.
The supplementary registered 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19 by Worker 6 and at PDF17–19 by Worker 1069. Their
nearby chain correction (for the 2010 page 305) is already incorporated in
the 2026 proof of the preceding simple-quotient proposition, which uses an
arbitrary chain. The next entry concerns a later functor passage. These pages
contain no correction of the A.VII lemma. This is a limited observation, not
an exhaustive absence claim.

## Exact proposition

For independent source-family universe `r`, Hom universe `v` and object
universe `u`, the full declaration has outer parameters
`(C : Type u) [Category.{v} C] [Abelian C]` and body

```lean
IsSourceGrothendieck.{r} C → SourceAB6 C →
  ∀ (X : C) [Small.{r} (Subobject X)],
    (IsSemisimpleObject X ↔ IsCompletelyReducible.{r} X) ∧
    (IsSemisimpleObject X ↔ IsSumOfSimpleSubobjects X) ∧
    (IsSumOfSimpleSubobjects X ↔ EverySubobjectHasComplement X)
```

The source hypotheses and the object's size presupposition are inside the
proposition. No equivalence appears among the premises.

All four predicates are imported from
`Langlands.CategoryTheory.RenardSemisimplicity`, unchanged:

| Predicate | Actual meaning |
| --- | --- |
| `IsCompletelyReducible.{r} X` | There are an index type `I : Type r`, objects `S i`, and maps `S i ⟶ X`, each `S i` simple, such that their actual cofan with vertex `X` is a colimit. |
| `IsSemisimpleObject X` | The existing alias `IsCompletelyReducible.{max u v} X`. |
| `IsSumOfSimpleSubobjects X` | `IsLUB {P : Subobject X \| Simple (P : C)} ⊤` in the existing categorical subobject order. |
| `EverySubobjectHasComplement X` | For every actual subobject `P`, there is an actual subobject `Q` such that `coprod.desc P.arrow Q.arrow` is an isomorphism. |

Complete reducibility asserts an actual coproduct universal property, allowing
the empty family. Its published `iff_exists_iso_sigma` expresses the equivalent
formulation with an isomorphism to a chosen coproduct. The sum condition uses
the full set of simple subobjects and asserts existence of its least upper
bound equal to top. The complement condition uses the canonical map from
the binary coproduct of the two chosen subobjects, induced by their actual
inclusions. It does not replace this comparison with an arbitrary abstract
isomorphism. Binary coproducts already exist in an abelian category.

The second and third conjuncts express the source's three-way equivalence
using the existing semisimple alias for condition (i). The first conjunct is
an internal comparison requested to connect that alias with complete
reducibility at the source-family size. It is additional packaging of the
source result, not another assertion printed in the book.

## Source size and the existing alias

The source works with set-indexed families without distinguishing universe
levels. Here `IsSourceGrothendieck.{r} C` supplies only `r`-indexed coproducts
and the corresponding directed-intersection law. Mathlib's actual
`Subobject X` lies in `Type (max u v)`. The explicit assumption
`Small.{r} (Subobject X)` says that this full subobject type is equivalent to a
type in `Type r`; it does not equate `r`, `u` and `v`.

This assumption permits reindexing the source's families of subobjects and
their subfamilies at size `r`, including the families used in the Zorn
arguments. Subobjects of a subobject of `X` embed into `Subobject X`, so the
same size bound is available for those steps. No category-wide smallness,
generator, finite length, finite dimensionality, Noetherianity or global
`HasCoproducts.{max u v} C` assumption is added. At
`r = max u v`, the displayed smallness instance is automatic.

The alias comparison also has an intrinsic size rationale. In a coproduct
of simple objects, the injections are split monomorphisms. Distinct indices
give distinct subobjects: projection to one summand would otherwise force
its nonzero identity to be zero. Thus the index injects into the subobject
type of the coproduct vertex. Given smallness of `Subobject X`, transport
across the coproduct isomorphism and reindexing of the colimit can reduce a
complete-reducibility witness to size `r`. Conversely, the index of an
`r`-sized witness injects in the same way into `Subobject X`, which lies in
`Type (max u v)`, so that witness can be reindexed at size `max u v`. The
first conjunct asks for this comparison as part of the future proof; the
present statement does not supply that proof.

## Source proof boundaries and remaining work

The source proves (i) implies (ii) directly, obtains (iii) from (ii) by
maximizing a family of simple subobjects disjoint from the specified
subobject, and proves (iii) implies (i) by a maximal direct sum and a
nonzero residual complement. These are proof obligations of a separate
exact-target proof task.

Two reading details are already documented in the imported definition's
Markdown. The finite-type subobject used to obtain a simple subobject must
be nonzero; that step is needed only in the nonzero residual complement.
Zero objects remain covered through the empty direct sum. Also the phrase
about proper subobjects of `F` in that paragraph refers to the finite-type
object denoted `E′`, before `F` is introduced. These internal reading
observations do not change the lemma's statement.

This unit states the lemma, with the explicit size convention and alias
comparison described above. The following corollary about subobjects of
semisimple objects is a separate result. Module and representation adapters,
category decompositions and the other whole-book obligations remain
separate. Worker 6 authored this initial statement pair. Worker 1069
rechecked it against the source, errata and compiled declaration, and
revised this Markdown.
