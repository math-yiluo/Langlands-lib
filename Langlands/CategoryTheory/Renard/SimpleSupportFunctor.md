# Canonical functoriality of Renard's supported sums

Authors: Worker 6, who wrote the construction and its first checked draft,
and Worker 1046, who independently rechecked the draft, the public imports
and the source passages and adopted the pair. This is an internal
(derived) construction prerequisite for using
the actual supported sums as category decomposition components. It
constructs their canonical maps, the resulting ambient endofunctor and
its inclusion into the identity. It supplies no support/maximality theorem
for the sum, splitting theorem or category equivalence.

The source of the underlying supported sums is David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, A.IX, printed268/PDF274. The registered original
`renard-2026-representations-groupes-reductifs-padiques` has SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`
and resides at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both authors read the complete page for this construction. It defines the
supported sums and splitting and states the later subquotient lemma; it
does not separately state the functor constructed here.

The mathematical derivation uses the already published general
epimorphism transport
`simpleSubquotientClasses_subset_of_epi` from
`Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`.
It generalizes to an arbitrary epimorphism the quotient half
`JH(M/M') ⊆ JH(M)` of Renard A.VI.3, unnumbered Lemma (i),
printed264/PDF270, whose original passage both authors read.
The implementation below is a derived construction, not a claim that
Renard explicitly states this functor or that all his later decomposition
theorems hold under these weaker assumptions.

The known source-errata audit found no dedicated current errata file in
the project locations; exhaustive absence is not claimed. The different
edition supplementary source `renard-2010-corrections-complements`,
SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, was read by both authors. Its supported-sum letter correction
(page 310 of the 2010 edition: read `E` and `E_S` for `M` and `M_S`) is
already incorporated in the 2026 text and supplies no additional
functoriality claim.

## Objects and exact existence assumptions

Let `C : Type u` with `[Category.{v} C]` and `[Abelian C]`, with
independent object and morphism universes. The set `S` is any actual set
of `ObjectClass C`; no subset restriction to `simpleClasses C` is needed
for this internal construction.

The public `simpleSupportSum S X` is unchanged: it is the image subobject
of the coproduct map from all actual supported subobjects of `X`.
For a map `X ⟶ Y` the construction requires exactly the coproducts of
the full supported-subobject families for these two objects.
For composition it also requires that of the intermediate object.
The functor and inclusion use the corresponding instances for every
actual object, expressed as
`∀ X : C, HasCoproduct (fun P : simpleSupportSubobjects S X => (P : C))`
with the explicit subobject coercion in Lean.

This is objectwise existence of those particular coproducts. It is no
global `HasCoproducts.{max u v} C` assumption, which would collapse the
Hom types to subsingletons. There is no equality of universes, global
smallness, well-poweredness, generator, finite-length or concrete-category
condition. Precise source-size adapters for these families are separate.

## Implemented construction and laws

For an actual `f : X ⟶ Y` and each supported subobject `P` of `X`, let
`g = P.arrow ≫ f`. The actual image subobject of `g` is supported on `S`:
the canonical factor map from `P` to this image is an epimorphism, so the
published transport puts each of its simple subquotient classes into the
classes of `P`, hence into `S`.

The public member bound therefore places this image below
`simpleSupportSum S Y`. Composing the image factor map with the inclusion
of this bound gives a factorization of `P.arrow ≫ f` through that sum.
Mathlib's pullback comparison places `P` below the pullback of the sum
along `f`. The public least-upper-bound law, applied to every such `P`,
then proves `simpleSupportSum_le_pullback`.

`simpleSupportSumMap S f` is the actual comparison into that pullback,
followed by its actual projection to `simpleSupportSum S Y`.
The pullback square and subobject comparison identities show

`simpleSupportSumMap S f ≫ (simpleSupportSum S Y).arrow =
(simpleSupportSum S X).arrow ≫ f`.

The inclusion into `Y` is a monomorphism. Cancellation proves uniqueness
of the map with this property and the identity and composition laws.
These are the short defining laws of the construction.

`simpleSupportSumFunctor S` has the actual supported-sum objects and
these actual maps. `simpleSupportSumInclusion S` has the actual subobject
inclusions as components, with naturality given by the displayed square.
Its components are monomorphisms because they are subobject inclusions.
The object, map and component evaluation laws are definitional.

The proof never assumes that the full supported sum is itself supported.
It uses support only for each member of the defining family and its
image under the particular morphism. Thus it needs no source
Grothendieck or AB6 hypotheses and no pending sum-identity, support,
closure, orthogonality or splitting theorem.

The endofunctor is ambient: no lift to the supported full subcategory,
adjunction, exactness, idempotence, partition decomposition or product
equivalence is constructed here. Those require their own results.
