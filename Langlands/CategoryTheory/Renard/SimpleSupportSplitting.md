# Renard A.IX: canonical splitting by simple support

Authors: Worker 6 (construction design and original Lean/Markdown draft) and
Worker 1014 (independent source and import checks, adoption, declaration
inspection and submission). This definition unit gives the actual canonical
maps and the subset/partition splitting predicates. It proves only their short
intrinsic defining laws. It proves no object splits, no splitting theorem
for subquotients, and no category equivalence.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.IX, the boxed definition
on printed268/PDF274. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 6 read the complete page as extracted text and inspected it visually.
Worker 1014 independently recomputed the source hash, read PDF274–275
(printed268–269) in full and visually checked PDF274, including the preceding
supported sums, the boxed definition and the subsequent subquotient lemma.
That lemma is a separate statement and proof obligation. PDF275 begins A.X.

The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is a different edition. Worker 1014 recomputed its hash and read PDF18–19
in full, confirming the preceding audit: the supported-sum letter correction
is already incorporated in the 2026 text. No new correction to the splitting
definition is claimed. On 29 October 2026, Worker 1014 checked the live
[author books page](https://perso.pages.math.cnrs.fr/users/david.renard/) and
its linked errata. Their bytes match the registered snapshot
`renard-author-page-2026-10-26` (SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`)
and the registered 2010 errata, respectively. The books section links the
corrected French 2026 PDF and labels the separate errata for the 2010
edition; it contains no separate 2026 errata link. No dedicated project
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` was
found in the current published Library or project notes. These are bounded
checks, not an exhaustive absence claim.

## Actual maps and objects

The namespace is `Langlands.Renard`, with `C : Type u`,
`[Category.{v} C]`, `[Abelian C]`. For partitions, `I : Type w` is
independent of both ambient universes. The principal declaration is
`Langlands.Renard.SimpleSupportPartitionSplitsCategory.{w,v,u}`. The public `ObjectClass C` is the
quotient of actual objects by actual isomorphism; `simpleClasses C` is its
subset of classes of actual simple objects. The public `simpleSupportSum S X`
is the image of the coproduct map to `X` from the full subtype
`simpleSupportSubobjects S X`. Its underlying object and actual inclusion
are used unchanged.

`simpleSupportComplement S` is exactly `simpleClasses C \ S`, rather than
the complement in all object classes. Its membership law is definitional,
and disjointness with `S` follows by applying nonmembership to membership.

`simpleSupportSubsetDesc S X` is the actual
`biprod.desc (simpleSupportSum S X).arrow
(simpleSupportSum (simpleSupportComplement S) X).arrow`.
Its domain is the actual ambient binary biproduct. The two restriction
laws follow from the binary biproduct universal property.

`simpleSupportPartitionDesc S X` is
`Sigma.desc (fun i => (simpleSupportSum (S i) X).arrow)`.
Its domain is the actual coproduct of the actual supported sums. The leg
law follows from the coproduct universal property. Each construction
requires only the coproducts of the full supported-subobject families that
it uses, and the partition construction also requires the one outer
coproduct. Binary biproducts already exist in an abelian category.

## Predicate meanings

`SimpleSupportSubsetSplits S X` asserts:

- `S ⊆ simpleClasses C`;
- existence of the coproducts defining both actual supported sums;
- invertibility of the actual `simpleSupportSubsetDesc S X`.

This interprets the source's `E = E_S ⊕ E_(Irr \ S)` by the canonical
map determined by the inclusions. An unrelated isomorphism to another
direct sum is insufficient.

`IsSimpleSupportPartition S` asserts pairwise disjointness and the exact
set equality `(⋃ i, S i) = simpleClasses C`. Its short `subset` lemma
places membership in one block into that union and uses the equality.
Empty blocks are allowed. An empty index is allowed and its union must
still equal the full simple-class set.

`SimpleSupportPartitionSplits S X` asserts that `S` is such a partition,
that every coproduct defining its actual supported sums exists, that their
outer coproduct exists, and that `simpleSupportPartitionDesc S X` is
invertible. It interprets the source's displayed direct sum using the
canonical inclusions. No nonempty or finite index condition is added.
An empty index therefore uses the actual empty coproduct.

`SimpleSupportSubsetSplitsCategory S` and
`SimpleSupportPartitionSplitsCategory S` respectively assert the
corresponding object predicate for every actual `X : C`. Every predicate
is a `def` returning `Prop`.

The `simpleSupportSubsetSplits_iff` and
`simpleSupportPartitionSplits_iff` lemmas expose these exact definitions
when the particular coproduct instances are already available.
`HasCoproduct` is proposition-valued, so proof irrelevance identifies the
chosen existence proofs; the underlying sums and maps do not change.
The forward direction extracts the existential witnesses and their
invertibility; the reverse direction supplies the available instances.

## Existence, source size and scope

Existence of the required coproducts is a conjunct expressed by existential
binders in the splitting predicates. It is never an implication from
coproduct existence. In particular, a category lacking a required
coproduct does not satisfy a splitting predicate merely because there
is no instance. The category predicates assert this for every object.
No global coproduct-existence assumption is imposed.

The full supported-subobject subtype lies in `Type (max u v)`. No
`HasCoproducts.{max u v} C` is assumed: that global condition forces
all Hom types to be subsingletons. A particular coproduct of this full
family can instead be obtained from source
`IsSourceGrothendieck.{r} C` and exactly
`Small.{r} (simpleSupportSubobjects S X)`, at an independent source family
universe `r`, as in the public support/maximality statement. A partition
also needs its outer index coproduct at the appropriate source size.
These are precise adapters to the source existence presuppositions,
not supplied theorems or extra conclusion-bearing fields here.

Renard introduces the definitions under the source Grothendieck and AB6
hypotheses. Forming the maps and predicates needs only the weaker
abelian setting and the particular coproducts made explicit above.
This generic definition is an implementation extension which specializes
to the source setting. It claims no later theorem under weaker
hypotheses and assumes no support, maximality, orthogonality or closure
result for the supported sums.

The source assertions about support and maximality of `E_S`, closure and
abelianness of the supported full subcategories, Hom orthogonality,
disjoint intersections, splitting of subquotients, and categorical
product equivalence remain separate obligations with their existing
owners. This construction unit discharges none of them.

## Development verification

Worker 1014 checked the adopted module and a private declaration-printing
probe in approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Diagnostic `6f65c2cf-ba26-4ee5-91b1-500da7d75c2f` completed successfully
with zero errors and warnings. It printed all eight unapplied definitions
and the five predicate axiom lists. The principal predicate was inspected
as a definition returning `Prop`, with independent level parameters
`w, v, u` and exactly `propext`, `Classical.choice` and `Quot.sound`.
The bodies use the actual `biprod.desc` and `Sigma.desc` maps and existentially
bind the required coproduct proofs. The original supplied Lean code was
adopted without changes. The entire five-module project import closure
and its paired Markdown were compared byte for byte with the current Library
and remain unchanged. The diagnostic probe stays private. These development
checks do not supply independent semantic acceptance or publication.
