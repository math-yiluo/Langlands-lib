# Bounded morphisms with monotone chosen atlas charts

Author: Worker 36.

This module constructs a category of supplied indexed affinoid-atlas
presentations with monotone chosen target charts and compatible bounded
pullbacks. It constructs unique local pullbacks when an admissible target
chart lies inside the chosen target, proves their chart formula and
restriction naturality, and realizes the published disjoint affinoid-family
category in this category. The latter functor retains the actual continuous
spectrum diagram exactly.

## Sources and provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.2, Definition 1.2.3 and Remark 1.2.4(i), printed page 16 / PDF
page 13, gives the affinoid-atlas and bounded restriction conventions.
Definition 1.2.7, printed page 18 / PDF page 15, requires a continuous map,
a target chart for each source chart, and compatible affinoid maps for
**every** chart pair satisfying image containment. Proposition 1.2.8 and
the subsequent composition discussion use extended atlases and gluing.
Registered source: `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original PDF pages 13–15 were reread for this unit; the extracted
page-15 header is erroneous, while the previously rendered original
confirms printed page 18.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.1.11, printed/PDF page 8, defines affinoid spaces by dualizing
bounded homomorphisms of affinoid algebras. Definition 2.2.1, printed/PDF
page 9, gives the affinoid-domain image and unique-factorization property.
Registered source: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Both original pages were read. No source-specific errata note was found
in the available workspace, Library or shared project notes.

This is derived presentation infrastructure, not a replacement definition
of the source's strong morphisms. Monotonicity of the selected target
charts is an additional condition on the chosen data. The category keeps
those choices as part of its arrows. Its local-factorization construction
covers only target charts contained in the chosen target. It does not
supply all admissible pairs of Definition 1.2.7 or the extended-atlas
gluing needed for their general composition. The concrete disjoint-family
realization uses previously constructed actual quotient algebras, spectra,
charts and bounded maps; no analytic structure on its output space is
assumed.

## Supplied atlases and bounded-map uniqueness

Let `K : Type u` be a complete ultrametric normed field. The space universe
`v` and chart-index universe `w` are independent of `u` and each other.
`AffinoidAtlasPresentation.{u,v,w} K` consists of a bundled topological
space `space : TopCat.{v}` and a supplied
`IndexedAffinoidAtlas.{u,v,w} K space`.

The imported atlas has actual presented positive-polyradius affinoid
quotient algebras, embedded spectrum charts, injective indexing of their
images, a compact chart net, and actual bounded restrictions satisfying
the chart formula, full presented-affinoid-test factorization, identity
and composition laws. This module does not construct such data on every
topological space. It bundles existing atlas data so that their maps can
be composed and compared.

For an atlas `a`, indices `i,j` with chart `i` contained in chart `j`,
and any presented affinoid test algebra `R`,
`IndexedAffinoidAtlas.restriction_hom_ext` proves

```text
ψ ∘ restriction(i,j) = χ ∘ restriction(i,j)  implies  ψ = χ,
```

for bounded maps `ψ,χ : a.algebra i → R`. To apply the domain universal
property, use `ψ ∘ restriction(i,j)` as its input. The restriction chart
formula shows that its spectrum image lies in chart `i`. Both `ψ` and
`χ` factor this same bounded map, so uniqueness equates them. This is
algebraic factorization uniqueness; no faithfulness of spectral points
is asserted or used.

## Chosen chart maps and their category

For presentations `A,B`, `AffinoidAtlasPresentation.Hom A B` retains:

- `baseMap : C(A.space,B.space)`;
- `indexMap : A.atlas.Index → B.atlas.Index`;
- `index_mono`, carrying every containment of source chart images to a
  containment of their selected target chart images;
- `pullback i : BoundedAlgHom K (B.atlas.algebra (indexMap i))
  (A.atlas.algebra i)`;
- `chart_comm`, identifying the target chart applied to the spectrum
  comap of `pullback i` with `baseMap` applied to the source chart;
- `restriction_comm`, equating the two bounded maps around each
  containment square.

Write `r_A(i,i')` for a source restriction and `F_i` for the chosen
pullback. The square condition is

```text
r_A(i,i') ∘ F_i' = F_i ∘ r_B(indexMap i,indexMap i').
```

`Hom.ext` proves equality from the continuous-map equality, index-function
equality and heterogeneous equality of the dependent pullback families.
The remaining fields are proofs. `image_chart_subset` follows directly
from `chart_comm` and proves actual image containment in the selected
chart.

`Hom.id` uses continuous and index identities and the actual bounded
identity on each chart algebra. `Hom.comp f g` uses `g.baseMap.comp
f.baseMap`, index function `g.indexMap ∘ f.indexMap`, and bounded pullback

```text
(f.pullback i).comp (g.pullback (f.indexMap i)).
```

Monotonicity composes. The chart formula follows by applying the chart
formulas of `g` and then `f` to the nested spectrum comap. Reassociation
and the two bounded restriction-square equalities prove the composite
restriction square. Extensionality and definitional bounded-map identity
and associativity laws give the category laws. The `baseMap_id`,
`indexMap_id`, `pullback_id`, and corresponding composition lemmas expose
the formulas. `spaceFunctor` retains the given spaces and continuous maps.

## Constructed pullbacks to smaller target charts

Fix `f : Hom A B`, source index `i`, and target index `j`. Assume
`hj` says chart `j` is contained in chart `f.indexMap i`, and `hf` says
`f.baseMap` sends chart `i` into chart `j`.

`localPullback_existsUnique` applies the target atlas domain property to
`f.pullback i`, with test algebra `A.atlas.algebra i`. The chart formula
and `hf` verify the required spectrum image condition. It proves a unique
bounded map `ψ : B.atlas.algebra j → A.atlas.algebra i` satisfying

```text
ψ ∘ r_B(j,f.indexMap i) = f.pullback i.
```

`localPullback` chooses that unique map;
`localPullback_comp_restriction` states its equation and
`localPullback_unique` its uniqueness. `localPullback_chart` uses the
factorization equation and the target restriction chart formula to
identify its actual spectrum map with `f.baseMap` on source chart `i`.
`localPullback_target` specializes to the selected target and uses the
bounded identity restriction to recover `f.pullback i`.

For source containment `i ⊆ i'` and target containment `j ⊆ j'`, assume
both target charts satisfy their respective smaller-target and image
conditions. `localPullback_naturality` proves

```text
r_A(i,i') ∘ localPullback(i',j')
  = localPullback(i,j) ∘ r_B(j,j').
```

Its proof precomposes with `r_B(j',f.indexMap i')` and applies the proved
`restriction_hom_ext`. On the left, factorization and the original
restriction square give `F_i ∘ r_B(f.indexMap i,f.indexMap i')`. On the
right, target restriction composition, monotonicity and factorization
give the same bounded map. This argument retains all bounded algebra
data, including nonreduced information and empty spectrum cases.

## Concrete disjoint-family functor

For `A : AffinoidFamily.{u,v} K`, `AffinoidFamily.atlasPresentation A`
bundles its already constructed actual topological sum of quotient
spectra and `A.atlas`. Its space universe is `max u v` and its chart
index universe is `v`. Empty index types and empty component spectra
remain allowed; only nonempty components occur as atlas indices.

`AffinoidFamily.Hom.atlasMap f` uses the published actual `spectrumMap`,
selected nonempty `chartTarget`, and original bounded pullbacks
`f.pullback c.val`. Source chart containment forces equality of its
nonempty component indices. After this equality the target containment
is reflexive and the bounded restrictions are identities, proving both
`index_mono` and the bounded restriction square. The chart formula is
the componentwise spectrum formula.

`atlasMap_id` and `atlasMap_comp` use the published continuous spectrum
laws and the actual dependent bounded-map formulas. They assemble the
selected entry definition `AffinoidFamily.atlasFunctor`. The equality
`atlasFunctor_spaceFunctor` proves

```text
AffinoidFamily.atlasFunctor ⋙ AffinoidAtlasPresentation.spaceFunctor
  = AffinoidFamily.spectrumFunctor.
```

The equality is definitional on objects and arrows. This functor discards
choices on empty family components when passing to nonempty atlas
indices; no faithfulness or equivalence is claimed.

## Scope

The general category has supplied actual atlas data as input. Its arrows
have monotone selected targets, and its constructed extra local maps need
the explicit smaller-target containment. The module does not construct a
general overlapping atlas, all strong morphisms, localization by atlas
refinement, a structure sheaf, analytic etale or quasi-etale sites, full
analytic automorphism continuity, or Harris tower spaces. These remain
separate obligations of the host analytic construction task.
