# Multiplicative spectra and bounded pullback

Author: Worker 36.

The original source is Vladimir G. Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), the retained 38-page author PDF.
Source ID: `berkovich-2009-trieste-analytic-spaces`.
Content SHA256:
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The Central Library pointer names
`Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
Printed and one-based PDF page numbers coincide.

Definition 1.2.3, page 4, defines the spectrum by nonzero bounded
multiplicative seminorms. Exercise 1.2.4 on the same page normalizes the
value at one and replaces the positive bounding constant by one.
`BanachSpectrum` uses Mathlib's actual `MulRingSeminorm`, including
nonnegativity and the value one at one, together with this constant-one
bound. Conversely `ofBounded` converts any such seminorm with an
arbitrary positive bound into a spectrum point. Its construction uses
`contraction_of_isPowMul_of_boundedWrt`: applying the bound to powers
and taking roots removes the constant. This normalization excludes the
zero seminorm; the zero ring consequently has no point.

Definition 1.2.5, page 4, is implemented by the topology induced from
the function space of real-valued evaluations. Each evaluation is
continuous, and this is the weakest such topology. The source uses
nonnegative real values; using real-valued functions with proved
nonnegativity gives the same topology. Completeness is unnecessary for
these definitions and elementary constructions, so they are available
for every normed commutative ring. On complete rings they give the
source's Banach spectrum.

`BoundedRingHom` consists of actual unital ring homomorphisms with a
positive linear norm bound. Composition multiplies the two positive
constants. `comap` composes a seminorm with such a ring map, verifies
its seminorm laws, and applies `ofBounded`. The induced map on spectra
is continuous coordinate by coordinate. The category `BanachRing`
bundles complete normed commutative rings with these bounded maps;
`banachSpectrumFunctor` is the resulting contravariant functor to
topological spaces. This categorical packaging is an internal
formalization of bounded pullback, derived from Definitions 1.2.1,
1.2.3 and 1.2.5, pages 3-4. It does not impose an analytic structure.

`fieldPoint` is the given multiplicative norm on a normed field.
`BoundedRingHom.scalarHom` constructs the scalar map of a normed
algebra using the bound `max 1 (norm 1)`; no extra norm-one instance on
the algebra is required. The actual kernel ideal has carrier `x a = 0`.
Its ideal laws use nonnegativity, subadditivity and multiplicativity,
as in the paragraph after Exercise 1.2.4. Primality and completed
residue fields are subsequent results. The primality statement is included
in the [spectrum properties target](Statement.md).

Finally `laurentLocus` names the subset cut out by upper and lower
evaluation inequalities. Exercise 2.2.2(i), page 9, is its
specialization to finite tuples and positive radii on an affinoid
algebra. The Lean subset definition also permits arbitrary index
types and real thresholds; it makes no compactness, finiteness or
representability claim in that greater generality. Proving an
affinoid-domain universal property requires the subsequent algebra
construction. No structure sheaf, analytic atlas, etale site or
cohomology object is supplied or assumed here.
