# Pullback of concrete ordinary-open affinoid sections

Author: Worker 36.

## Mathematical content

Let `K` be a complete ultrametric normed field, let `A` and `B` be presented
positive-polyradius affinoid algebras, and let `φ : BoundedAlgHom K A B` be an
actual bounded algebra homomorphism. Write `f : BanachSpectrum B → BanachSpectrum A`
for `BanachSpectrum.comap φ.toBoundedRingHom`. For every ordinary open `U` of
`BanachSpectrum A`, the selected definition
`RationalChart.OpenSections.pullback φ U` constructs an algebra homomorphism

```text
Sections U →ₐ[K] Sections (f ⁻¹' U).
```

Here `Sections` is the published algebra of families of actual rational quotient
algebra elements compatible under every actual bounded rational restriction.
The construction acts on those elements, including nilpotents. The spectral map
is used for locus containment and the choice of finite covers; equality of
sections is proved by rational algebra separation.

## Finite construction

For every rational target chart `e` with `e.locus ⊆ f ⁻¹' U`,
`pullbackRefinement φ U e` constructs a finite family `c.chart i → e`. Each
component has a source label `c.label i`, a rational chart contained in `U`, and
its image under `f` lies in the interior of that source chart's locus. The
relative interiors of the target components cover the whole locus of `e`.

The refinement uses `exists_rational_neighborhood` at each image point and
`FiniteOpenRefinement.ofOpenCover` on the compact target chart. The proved
identity `RationalChart.pullback_locus` turns subordination into the actual
bounded rational restriction `pullbackRefinementMap` from each target component
to the coefficient pullback of its source label. The local value is the source
component of the given section, transported by `pullbackMap` and then restricted
along this constructed arrow.

Compatibility of two such local values is proved in the actual rational
quotient algebra of their target intersection. The proof factors through the
intersection of the two source charts, uses
`pullbackRestriction_comp_pullbackMap`, the compatibility of the source
section, and uniqueness of actual bounded restriction arrows. The published
finite rational gluing theorem then gives `pullbackElement φ s e`.

## Local formula and algebra structure

`pullbackElement_local` proves the following formula. Let `d` be a rational
source chart contained in `U`, let `w` be any rational target chart, and suppose
there are actual rational restriction arrows

```text
h : w → e,    g : w → RationalChart.pullback φ d.
```

Then

```text
h.restriction (pullbackElement φ s e)
  = g.restriction (pullbackMap φ d (s.val d)).
```

The implemented proof covers `w` by its intersections with the finite refinement
of `e`. On each intersection, uniqueness of restriction arrows identifies the
two paths into `e`, the gluing equation identifies the descended element, and the
transport compatibility just proved identifies it with the component from `d`.
Finite rational separation proves equality on `w`. This argument applies to all
such `w`, not only the initially chosen refinement components.

`pullbackElement_restriction` uses this local formula and finite separation to
prove compatibility under every restriction between target charts.
`pullbackElementHom` proves the zero, one, addition, multiplication and scalar
laws by checking them on the finite refinement. Each refined component is the
composition of source evaluation, actual quotient transport and actual bounded
restriction, hence an algebra homomorphism. The selected `pullback` is the
product of these descended algebra homomorphisms, with codomain restricted to
the proved compatible-family subalgebra. `pullback_apply` records its component
formula, and `pullback_local` specializes the local formula to an entire target
chart.

## Ordinary restriction and structural maps

`pullback_restriction` proves equality of algebra homomorphisms for every
inclusion `U ⊆ V` of ordinary source opens:

```text
restriction (f ⁻¹' U ⊆ f ⁻¹' V) ∘ pullback φ V
  = pullback φ U ∘ restriction (U ⊆ V).
```

The proof uses a refinement subordinate to source charts in `U` for both sides,
then applies the local quotient formula and finite separation.

`pullback_fromBase` proves that the compatible family induced by an element
`a : A` pulls back to the compatible family induced by `φ a : B`. It uses the
published `pullbackMap_baseMap` equation and the structural-map equations of
the actual restriction arrows on the same finite refinement.

## Provenance and scope

This is an internal construction from `RationalOpenGluing`,
`RationalChartOpenRefinement` and `RationalChartBaseChange` and their published
finite rational descent, full-domain restriction and rational neighborhood
prerequisites. It introduces no additional original-literature assertion or
assumed analytic output. The proof route above describes the implemented Lean
proofs.

The construction retains arbitrary strictly positive real radii, trivial
valuations, nonreduced algebras, zero algebras and empty spectra. Finite covers
may be empty; the published gluing and separation statements include that case.
This module constructs the pullback algebra homomorphism and its local,
restriction and structural-map laws. Identity and composition laws, the maps of
stored sheaves and locally ringed spaces, unrestricted analytic atlases, and the
analytic etale and equivariant sites remain subsequent construction work.
