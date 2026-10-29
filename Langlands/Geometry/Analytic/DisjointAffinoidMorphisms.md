# Componentwise bounded morphisms of disjoint affinoid families

Author: Worker 36.

The module constructs a category of families of actual finite
positive-polyradius quotient algebras. Its arrows are chosen component
functions with bounded algebra pullbacks. It realizes them on the actual
disjoint unions of spectra and constructs compatible bounded maps for
every chart pair whose images have the required containment. Identity and
composition hold on the algebra maps themselves.

## Sources and provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.2, Definition 1.2.3 and Remark 1.2.4(i), printed page 16 / PDF
page 13, gives the affinoid atlas and restriction conventions used by the
imported `DisjointAffinoidAtlas` construction. Definition 1.2.7, printed
page 18 / PDF page 15, specifies a continuous map carrying each source
chart into a target chart, together with compatible affinoid morphisms
for every chart pair satisfying the containment. The subsequent paragraphs
on that page construct composition. The general construction there uses
extended atlases and gluing; the disjoint-family case below has an explicit
componentwise composition. Registered source:
`berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.1.11, printed/PDF page 8, defines affinoid spaces as the
category opposite to affinoid algebras and bounded homomorphisms. This
fixes the contravariant direction of the component pullbacks and their
composition. Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Both passages were read in the original files, and their fingerprints
were verified. No corresponding erratum was found in the available project
notes.

The category of chosen families, spectrum functor and explicit local-map
formulas are derived constructions. They realize the cited strong-morphism
data for the published disjoint atlases over a complete coefficient field.
They retain the chosen component function, including its values on empty
components. The construction therefore makes no assertion that this
category is equivalent to all strong morphisms of the underlying atlases.

## Objects and bounded morphisms

`Langlands.Analytic.AffinoidFamily K` consists of an index type and a
family `algebra` of `PresentedAffinoidAlgebra K`. These are the published
actual closed-ideal quotients of finite weighted Tate algebras. Arbitrary
positive radii, the empty index type and empty component spectra are
allowed.

The coefficient field is an ultrametric normed field. The field universe
`u` and index universe `v` are independent. `AffinoidFamily.Space A`
is the actual dependent sum of the spectra, in universe `max u v`,
with the topological sum topology. Over complete `K`,
`AffinoidFamily.atlas A` is the previously constructed
`DisjointAffinoidAtlas.atlas A.algebra`. Thus objects do not assume an
analytic structure on an arbitrary input space.

For families `A` and `B`, `AffinoidFamily.Hom A B` consists of

- `indexMap : A.Index → B.Index`;
- for every `i`, an actual bounded `K`-algebra homomorphism
  `pullback i : B.algebra (indexMap i) → A.algebra i`.

The bounded maps retain their scalar compatibility and positive norm
bounds. `Hom.ext` proves equality from equality of the component functions
and heterogeneous equality of their dependent families of pullbacks.

The category identity uses the identity component function and bounded
identity homomorphisms. For `f : A ⟶ B` and `g : B ⟶ C`, the component
function is `g.indexMap ∘ f.indexMap`, and the pullback at `i` is

```text
(f.pullback i).comp (g.pullback (f.indexMap i)).
```

The category laws follow from function equality and pointwise equality
of the bounded algebra homomorphisms. `pullback_id` and `pullback_comp`
expose these formulas.

## Actual spectrum realization

`Hom.spectrumMap f` sends `(i,x)` to the point in component
`f.indexMap i` obtained by pulling back the seminorm `x` along
`f.pullback i`. Its continuity follows on each summand from continuity
of the published spectrum comap and of the target component inclusion.
The universal continuity criterion for a topological sum then gives
continuity of the whole map. `spectrumMap_fst` records its component.

`spectrumMap_id` and `spectrumMap_comp` prove agreement with the continuous
identity and composition. `AffinoidFamily.spectrumFunctor` packages this
as a functor to `TopCat.{max u v}`.

These functor laws accompany algebraic category laws. The construction
does not infer equality of algebra homomorphisms from equality on spectral
points, which could discard nonreduced information.

## Compatible local maps on all chart pairs

Charts in the published disjoint atlas are exactly the nonempty component
spectra. `Hom.chartTarget f c` constructs the target chart of a source
chart `c`: choose a source spectrum point using the defining nonemptiness
of `c`, and pull its seminorm back along the actual bounded algebra map.
This proves that the chosen target spectrum is nonempty. No nonemptiness
assumption is imposed on the original family.

`spectrumMap_chart` gives the formula on component charts, and
`image_chart_subset` proves that every source chart maps into its
constructed target chart. `chartTarget_id` and `chartTarget_comp` show
that these targets respect the category operations.

For any source chart `c` and target chart `d` with the required image
containment, `chartTarget_eq` proves `f.chartTarget c = d`. Indeed, the
image of a point of `c` lies in both target components. The published
disjoint-chart intersection lemma then identifies their indices.

`localPullback f c d h` transports `f.pullback c.val` along that equality.
Its domain is the algebra of `d`, and its codomain is the algebra of `c`.
This constructs a local map for every admissible chart pair.
`localPullback_target` identifies it with the original pullback in the
chosen target chart. `localPullback_chart` proves that its spectrum comap
realizes the given continuous map in the two charts.

`localPullback_naturality` proves compatibility with restrictions in both
the source and target. For `c ⊆ c'` and `d ⊆ d'`, its equation is

```text
restriction(c,c') ∘ localPullback(c',d')
  = localPullback(c,d) ∘ restriction(d,d').
```

Both sides are bounded algebra maps from the algebra of `d'` to that of
`c`. The proof first uses the nonempty-component containment lemma to
identify `c = c'` and `d = d'`. The restrictions become bounded identities,
and bounded-homomorphism extensionality proves the equation on algebra
elements.

`localPullback_id` proves that the local map of the category identity
is the actual bounded identity. For every compatible triple of charts,
`localPullback_comp` identifies the local map of `f ≫ g` with the
contravariant composite of the local maps of `f` and `g`. It first
identifies the intermediate and final chart indices using
`chartTarget_eq`; the equality then follows from the componentwise
definition of composition.

## Verification and scope

The complete draft module and the exact entry declaration
`Langlands.Analytic.AffinoidFamily.spectrumFunctor` were checked with
the project's Lean service in check
`3755dae3-e8be-455b-a65c-fb1077b8555a`: Lake build succeeded with zero
errors and zero warnings. Inspection reported a definition with independent
universe parameters `u` and `v`, using only `propext`, `Classical.choice`
and `Quot.sound`.

This contribution supplies actual componentwise bounded maps and compatible
local affinoid morphisms on constructed disjoint atlases. Arrows include
chosen data on empty input components. General maps that split a source
component across several target components require a broader construction.
General atlas refinement and gluing, strong-morphism localization, structure
sheaves, étale and equivariant sites, and Harris's local tower remain
separate host-task obligations.
