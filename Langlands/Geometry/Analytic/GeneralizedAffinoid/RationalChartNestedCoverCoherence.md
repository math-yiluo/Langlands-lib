# Identity and composition of actual nested finite-cover transport

Author: Worker 56.

This module compares finite full-domain covers transported along identity and
composite rational-chart inclusions. It restores the targets using actual domain
isomorphisms, constructs cover isomorphisms and natural isomorphisms, and proves
the associated continuous-family and quotient-gluing equations. Component
comparisons retain their chosen indices and are identities on the actual
representing algebras.

## Inputs and conventions

The field `K` is a complete ultrametric normed field. The base
`A : PresentedAffinoidAlgebra K` and all domain algebras are the Library's
actual finite positive-polyradius Tate quotients by closed ideals, with their
chosen presentations. Rational charts retain arbitrary positive radii and
explicit unit generation. A chart arrow `f : d ⟶ e` stores a bounded algebra
map `e.algebra → d.algebra` over `A`; its actual spectrum map is a proved
closed embedding.

For `U : Domain K d.algebra`, the existing `nestedDomain f U` is a full
represented domain over `e.algebra`. Its representing algebra is exactly
`U.algebra` and its structural map is `U.baseMap.comp f.restriction`.
Its full affinoid-test universal property is supplied by the constructed
ambient extension and localization. Write

```text
N_f U = nestedDomain f U,
F_f   = nestedFiniteCoverFunctor f U,
H_f,U = nestedDomainLocusHomeomorph f U :
          U.locus ≃ₜ (N_f U).locus.
```

The forward map of `H_f,U` is `f.spectrumMap` on underlying points.
The cover `nestedFiniteCover f c` retains the component index set, each
component algebra, and its bounded restrictions.

`Domain.FiniteCover U` is the category of finite full-domain covers of a fixed
target `U`. A refinement remembers both a choice of coarser index for every
finer index and an actual bounded domain restriction. Equality of refinements
requires equality of the chosen index functions. Uniqueness of domain
restrictions determines their maps once these indices agree.

The existing comparisons

```text
a_id   = nestedDomainIdIso d U : N_(𝟙 d) U ≅ U,
a_f,g  = nestedDomainCompIso f g U : N_g (N_f U) ≅ N_(f ≫ g) U
```

have identity bounded restrictions on `U.algebra` in both directions.
The associated cover categories have different target parameters, so the
comparisons below explicitly restore the target before constructing a cover
isomorphism.

The target `Y : Type v` of continuous maps is arbitrary, in an independent
universe, with no separation hypothesis. `CompatibleFamily c Y` means a
continuous map on each component locus, with equal values whenever the
underlying points in the ambient spectrum are equal.

## Target restoration for actual finite covers

For an actual domain isomorphism `a : U ≅ V`,
`Domain.FiniteCover.changeTarget a c` has target `V`, the same size and
component domains as `c`, and component inclusions `c.map i ≫ a.hom`.
Coverage follows by applying the locus containment supplied by `a.inv`
and then using `c.covers`. The size, object and map projection lemmas expose
these data.

`changeTargetRefinement a r` retains the chosen index function and every
actual component arrow of `r`. `changeTargetFunctor a` bundles the
construction into a functor. Identity and composition follow from
`Refinement.ext` with reflexive equality of indices. The index and spectrum-map
projection lemmas state that the refinement's choice of indices and its map on
the disjoint union of component spectra are unchanged.

`changeTarget_componentMap` and `changeTarget_totalMap` identify the maps
from each actual component spectrum and from their disjoint union:
the new map is the old map followed by `a.hom.locusMap`. These are definitional
equalities of the constructed continuous maps.

`changeTargetFamilyEquiv a c` is the identity equivalence on compatible
families. Both the component-locus types and their agreement condition are
unchanged by target restoration. In particular, no equality between the two
cover structures is asserted.

`changeTargetFamilyEquiv_gluingEquiv` states that restriction of a global
continuous map transforms by precomposition with `a.inv.locusMap`:

```text
changeTargetFamilyEquiv a c (c.gluingEquiv p)
  = (changeTarget a c).gluingEquiv (p.comp a.inv.locusMap).
```

The proof compares every component map on each locus point. Both paths have
the same underlying spectrum point.

For a compatible family `p`, `glue_changeTargetFamily` states

```text
(changeTarget a c).glue p.val p.property
  = (c.glue p.val p.property).comp a.inv.locusMap.
```

This is an equality of the actual quotient-lift glues from `DomainGluing`.
The proof uses `glue_unique`: the proposed right side restricts to `p` on each
component, by `c.restrict_glue` and the identity of underlying locus points.

The helper `glue_changeTarget_pullback` allows an additional actual refinement
`r : Refinement (changeTarget a b) c`, where `b` covers `U` and `c` covers `V`:

```text
b.glue (r.pullback p).val (r.pullback p).property
  = (c.glue p.val p.property).comp a.hom.locusMap.
```

The pulled-back family can be used on `b` because restoration retains its
component loci and compatibility predicate. The proof combines the preceding
target-restoration glue equation with the existing
`Refinement.glue_pullbackFamily`, and evaluates the resulting equality at
`a.hom.locusMap x`. Composing with `a.inv.locusMap` returns the original
point. No descended map is assumed.

## Identity and composition comparisons of covers

`nestedFiniteCoverIdIso d c` constructs

```text
changeTarget a_id (nestedFiniteCover (𝟙 d) c) ≅ c.
```

Both refinements choose the identity index function. Their component maps
are the respective directions of `nestedDomainIdIso d (c.obj i)`.
`nestedFiniteCoverCompIso f g c` constructs

```text
changeTarget a_f,g (nestedFiniteCover g (nestedFiniteCover f c))
  ≅ nestedFiniteCover (f ≫ g) c.
```

Its refinements again choose identity indices; the component arrows are the
two directions of `nestedDomainCompIso f g (c.obj i)`.
All inverse laws use `Refinement.ext rfl`. This checks equality of the retained
indices as well as the uniquely determined actual component arrows.

The four index lemmas expose both directions' identity choices. The four
restriction lemmas expose identity bounded maps on each original
`(c.obj i).algebra`. `nestedFiniteCoverIdIso_hom_spectrumMap` and
`nestedFiniteCoverCompIso_hom_spectrumMap` state that the forward comparison
refinements induce the identity continuous map on
`Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra`.
Their proofs keep the index fixed and compare the multiplicative seminorms
on each algebra element.

`nestedFiniteCoverIdNatIso d U` makes the first cover comparison natural
in every chosen refinement:

```text
nestedFiniteCoverFunctor (𝟙 d) U
  ⋙ changeTargetFunctor a_id ≅ 𝟭 (Domain.FiniteCover U).
```

`nestedFiniteCoverCompNatIso f g U` makes the second comparison natural:

```text
nestedFiniteCoverFunctor f U
  ⋙ nestedFiniteCoverFunctor g (N_f U)
  ⋙ changeTargetFunctor a_f,g
    ≅ nestedFiniteCoverFunctor (f ≫ g) U.
```

Each construction uses `NatIso.ofComponents` with the cover isomorphisms
just described. Its naturality equation follows from `Refinement.ext rfl`:
each path selects the original refinement's coarser index. The actual bounded
component arrows then agree by uniqueness.

The three component coherence equations
`nestedFiniteCoverCompIso_source_id_map`,
`nestedFiniteCoverCompIso_target_id_map`, and
`nestedFiniteCoverCompIso_assoc_map` reuse the corresponding proved domain
equations. The first two compare composition with identity-chart transport
with the appropriate transported or direct identity comparison.
For `f : d ⟶ e`, `g : e ⟶ h`, `k : h ⟶ j`, the third compares the two
component-arrow paths from `N_k (N_g (N_f (c.obj i)))` to transport along the
triple composite. Each path is explicitly built from the specified actual
domain comparisons. These are component equations with the index projections
above, rather than an additional bundled pseudofunctor construction.

## Locus inverses and compatible families

`nestedDomainLocusHomeomorph_symm_id` identifies `H_(𝟙 d),U.symm` with
`a_id.hom.locusMap`. Its proof evaluates the existing forward identity
equation at the inverse image and applies the homeomorphism inverse law.

`nestedDomainLocusHomeomorph_symm_comp` states, for
`x : (N_g (N_f U)).locus`,

```text
H_(f ≫ g),U.symm (a_f,g.hom.locusMap x)
  = H_f,U.symm (H_g,(N_f U).symm x).
```

The proof names the right-hand point `y`, proves that successive forward
homeomorphisms send `y` to `x`, and applies the existing forward composition
equation at `y`. Injectivity of `H_(f ≫ g),U` and its inverse law give the
claimed inverse equation.

Write `T_f,c = nestedCoverFamilyEquiv f c`. The existing family equivalence
precomposes the map on component `i` with `H_f,(c.obj i).symm`.
`nestedCoverFamilyEquiv_id` proves

```text
T_(𝟙 d),c p = (nestedFiniteCoverIdIso d c).hom.pullback p.
```

`nestedCoverFamilyEquiv_comp` proves

```text
T_g,(nestedFiniteCover f c) (T_f,c p)
  = (nestedFiniteCoverCompIso f g c).hom.pullback (T_(f ≫ g),c p).
```

These equalities use the unchanged compatible-family types for the
target-restored covers. Pullback goes from the direct cover to the restored
successive cover. Each proof compares compatible subtypes, then component
continuous maps, and finally applies the relevant inverse-homeomorphism
equation to the original component map `p.val i`.

## Actual quotient-gluing coherence

`glue_nestedCoverFamily_id` compares identity transport before target
restoration with the original glue precomposed by `a_id.hom.locusMap`.
`glue_nestedCoverFamily_comp` compares successive transport with direct
transport:

```text
(nestedFiniteCover g (nestedFiniteCover f c)).glue
    (T_g (T_f p)).val (T_g (T_f p)).property
  = ((nestedFiniteCover (f ≫ g) c).glue
       (T_(f ≫ g) p).val (T_(f ≫ g) p).property)
      .comp a_f,g.hom.locusMap.
```

The notation in this display suppresses the covers in the family equivalences.
The Lean declarations include them explicitly. Both proofs first apply
congruence to the corresponding compatible-family identity, then apply
`glue_changeTarget_pullback` to the actual comparison refinement.
Consequently the comparisons concern the existing maps descended through the
finite disjoint union of actual component spectra and its proved quotient
map. They do not supply a new gluing operation as an input.

## Source and construction scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.9, Definition 2.2.1, gives the full represented affinoid-domain
universal property, and Exercise 2.2.2(ii) gives positive-radius rational
quotients. Printed/PDF p.10, Fact 2.2.3(i) and Definition 2.2.7 supply the
represented-spectrum and affinoid-domain-embedding context. The finite
affinoid covering convention is immediately before Fact 2.2.6. These original
pages were read directly.

All comparisons in this module are internal consequences of the Library's
actual domain and cover constructions, the proved nested-domain identity and
composition comparisons, the actual locus homeomorphisms, and the existing
quotient-lift continuous gluing construction. They are not separately numbered
assertions in the cited original.

The chosen-presentation scope and explicit unit-generation hypothesis remain;
no equivalence with the source's absence-of-common-zeros condition is asserted.
Empty covers and loci, zero algebras, nilpotents, arbitrary positive radii, and
trivial valuations remain permitted. This module asserts no rational
flattening, Tate acyclicity, algebra or module descent, new coherence for the
arbitrary-cover inverse functor, analytic atlas construction, etale site,
equivariant site, or Harris tower specialization.
