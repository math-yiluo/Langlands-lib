# Full quasi-isomorphisms under directed strong composition

Author: Worker 36.

This module proves that full strong quasi-isomorphisms compose when the
intermediate and final original atlases have directed charts. It packages
these actual morphisms as a multiplicative morphism property in the
constructed category of directed atlas presentations.

The coefficient field `K : Type u` is complete and ultrametric. The ambient
space and chart-index universes `v` and `w` are independent of `u`. The
algebras are the Library's finite positive-polyradius Tate quotients by closed
ideals; every such presented algebra remains a test object for full domain
representation. No strictness or reducedness assumption is added.

## Original source and derived scope

The original is Vladimir Berkovich, *Etale cohomology for non-Archimedean
analytic spaces* (1993), literature ID `berkovich-1993-etale-cohomology`,
PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13, specify the
actual bounded domain restrictions of an atlas. Definition 1.2.7 and the
following composition construction, printed p.18 / PDF p.15, give strong
morphisms and their composition. Definition 1.2.9 and Proposition 1.2.10(b),
printed p.19 / PDF p.16, give full strong quasi-isomorphisms and assert their
closure under composition. These original passages were read directly.

The source constructs general composition by extending atlases and gluing
local morphisms. This module proves the directed original-chart instance
using the existing `compOfDirected` construction. A common containing
original chart replaces the finite covering in that construction. Full
representation is then descended to the prescribed final original chart by
a new algebraic lemma. This is a derived proof of the stated restricted
instance of Proposition 1.2.10(b). It does not assume the proposition or the
unrestricted gluing construction. The domain-composition theorem
`Represents.comp_of_injective` is imported from the published
`GeneralizedAffinoid.RationalChartDomainComposition` module.

## Inverse-image representation

`PresentedAffinoidAlgebra.Represents.of_comp_of_injective` takes bounded maps
`i : A → B` and `j : B → C`, a full representation of `U ⊆ M(A)` by `i`, a
full representation of `V ⊆ M(A)` by `j.comp i`, and injectivity of the
actual spectrum map `M(B) → M(A)` induced by `i`. It proves that `j` fully
represents the inverse image of `V` in `M(B)`.

Closedness is the continuous inverse image of closedness of `V`. The exact
spectrum range of the composite and injectivity of `M(B) → M(A)` identify
the range of `M(C) → M(B)` with that inverse image.

For every presented test algebra `R`, let `φ : B → R` be bounded with
spectrum image in this inverse image. Then `φ.comp i` has spectrum image in
`V`, so the composite representation gives a unique bounded lift
`ψ : C → R`. Its equation is initially only over `A`. The representation
by `i` identifies `ψ.comp j` with `φ`: they are two lifts of `φ.comp i`,
and this map has image in `U` because it factors through `i`. Thus the
required equation over `B` follows from bounded-factorization uniqueness.
Any other lift over `B` is also a lift over `A`, so composite uniqueness
proves it equals `ψ`. This argument compares the actual bounded algebra
maps and does not assume faithfulness of the spectrum construction.

## Embedded original restrictions and descent

`IndexedAffinoidAtlas.isEmbedding_restriction` proves that the spectrum map
of each original bounded atlas restriction is an embedding. Composing it
with the containing chart gives exactly the smaller original chart. Both
charts are embeddings, so cancellation of the containing chart gives the
result. Injectivity needed for inverse-image representation is therefore
proved from the actual chart square.

`StrongHom.represents_pullback_of_upper` starts with an admissible original
source chart `i` and target charts `j ⊆ q`. It assumes full representation
for the pullback into `q` and proves full representation for the pullback
into `j`. The strong-map compatibility equation
`pullback_comp_restriction` expresses the pullback into `q` as the pullback
into `j` composed with the original restriction from `q` to `j`. That
restriction represents its original domain and has the embedding proved
above. The inverse-image lemma therefore applies. Finally,
`restriction_chart` identifies its inverse-image locus with
`f.chartImageLocus i j`. The maps and the represented algebra stay the
original ones throughout.

## Composition at every admissible pair

`StrongHom.IsQuasiIso.compOfDirected` takes full quasi-isomorphisms
`f : A → B` and `g : B → C`, with directed charts on `B` and `C`. The source
atlas `A` need not be directed. Their ambient homeomorphisms compose.

Fix any admissible source chart `i` and final chart `k`. Target existence
chooses a `B`-chart `j` containing the image of `i` and a `C`-chart `q₀`
containing the image of `j`. Directedness of `C` supplies a common upper
chart `q` for `q₀` and `k`. The full domain representations of the bounded
pullbacks for `g` at `(j,q)` and `f` at `(i,j)` compose using the imported
`Represents.comp_of_injective`. Its spectrum injectivity hypothesis follows
from `g`'s proved local embedding as a quasi-isomorphism.

The exact formula `compOfDirected_pullback` identifies this composed bounded
map with the constructed composite's pullback into `q`.
`range_pullback` and the exact spectrum-range equation of the composed
representation identify its locus with the composite's chart-image locus.
The preceding upper-chart descent then gives full representation at the
originally prescribed `(i,k)`. Since this pair was arbitrary, the proof
retains the complete all-admissible clause of `IsQuasiIso`.

## The morphism property

`DirectedAtlasPresentation.quasiIsomorphisms` is the actual morphism property
`fun _ _ f => f.IsQuasiIso` on the existing directed strong-map category.
`quasiIsomorphisms_iff` records this definition. Its `IsMultiplicative`
instance uses the published identity quasi-isomorphism and the composition
theorem above with the bundled intermediate and final directedness proofs.
Thus it concerns the existing full strong maps and their actual category
composition.

This focused unit provides identity and composition closure in this directed
category. Unrestricted atlas extension, gluing and composition, Ore squares,
localization, analytic sheaves, etale and equivariant sites, and the Harris
tower remain further construction obligations.
