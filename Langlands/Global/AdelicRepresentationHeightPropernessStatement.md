# Continuity and properness of full adelic representation heights

`Langlands.Global.RepresentationGrowth.AdelicRepresentationHeightPropernessStatement`
is a proposition target about the existing full adelic representation height.
It quantifies over every number field `F` in an arbitrary universe, every actual
affine group scheme `G` over `Spec F`, every positive natural rank `N`, and every
matrix representation `rho : G -> GL_N`. It asserts two properties.

First, `adelicHeight F G rho` is continuous as a real-valued function on the
original `AdelicGroupPoints F G`. This part requires no injectivity, closed
immersion, reductivity, smoothness or finite-type premise on `G`.

Second, if `rho` is a scheme-theoretic closed immersion, expressed by the
existing `GroupScheme.IsClosedSubgroup rho`, that same height is an
`IsProperMap` to `ℝ`. This is Mathlib's topological proper-map predicate,
which includes continuity. In particular, inverse images of compact real
sets must be compact. The already proved `one_le_adelicHeight` gives a
lower bound of one at positive rank, so the properness assertion also
implies compactness of every sublevel set
`{g | adelicHeight F G rho g <= B}`: it is the inverse image of the
compact interval `[1,B]`, including when that interval is empty.
Properness here concerns the full point group before any rational or
split-centre quotient.

## Exact height and topology

The function is exactly `RepresentationGrowth.adelicHeight` from
`AdelicRepresentationHeight`. Its value is the product of the factors
`(N * infiniteLocal v) ^ v.mult` over all infinite places and the finite
product of `finiteLocal v` over all finite places. Each local maximum
includes every entry of the represented matrix and its inverse.
The finite completion norms are the existing normalized norms, and the
infinite factors retain their existing multiplicities.

The positive-rank local lower bounds and the actual adelic conditions on
the matrix entries and inverse entries make the finite-place factors at
least one and equal to one outside a finite set for each point. Pointwise
finite support alone does not prove continuity of that finite product;
a proof must control the support on suitable restricted-product
neighborhoods.

The source carries its existing affine point topology over the actual
adele ring. The representation map is the existing continuous
`adelicMatrix`. The target does not replace this topology by the
unrestricted product of the local point groups or require a new choice of
integral model. The exact unscaled `adelicSourceNorm` is related to this
height by the already proved fixed scalar identity. This file does not
separately state continuity or properness for that unscaled function.

## Source and derived scope

Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
(6.3)–(6.4), printed pp.158–159 (PDF pp.172–173), give the inverse-inclusive
matrix norm. Equations (6.7)–(6.8), printed p.161 (PDF p.175), give its
full local product and explain the almost-everywhere unit factors.
Proposition 2.4.10, printed pp.61–62 (PDF pp.78–79), identifies affine
finite-type adelic points with the restricted product from a model.
Theorem 2.4.14(a),(c), printed p.64 (PDF p.81), records continuity of
point maps and closed embeddings from closed immersions.
The complete retained author errata makes no correction to these passages.

The present statement is an internally derived topological target for the
Library's dimension-scaled height. Those source passages supply its norm
and topology conventions; they do not directly state properness of this
real-valued height. In particular, Theorem 2.4.14(d) concerns point maps
induced by proper scheme morphisms and does not prove this height target.
The unconditional continuity assertion extends to arbitrary affine `G`
because its height is pulled back along the existing continuous matrix
map. For the closed-embedding assertion, a closed subgroup of the
finite-type general-linear scheme is itself of finite type, so that part
does not introduce an additional non-finite-type properness claim.

A prospective proof can first establish continuity and compact sublevels
of the standard full adelic matrix height. At finite places the normalized
valuation values and finiteness of number-field prime ideals of bounded
absolute norm should confine the nonintegral factors in a bounded
sublevel to finitely many places. Bounds on both a matrix and its inverse
then place it in a compact set of the actual units topology. At infinite
places the dimension scaling bounds each factor below by one, so a
bounded global product bounds all entries and inverse entries.
Closedness of the matrix-inverse identity supplies the relevant compact
matrix locus. A closed embedding on actual adelic points would then
transfer properness to `G`. These are proposed proof steps, not premises
or proved exports of this file.

## Boundary

This file defines only the proposition and proves neither continuity nor
properness. It assumes no supplied matrix-height properness result and no
height-domination theorem. The earlier archimedean-height continuity and
compactness of the finite integral subgroup do not alone establish this
target. Reduction theory, quotient finite volume, growth independence,
cuspidal estimates and square integrability remain separate obligations.
