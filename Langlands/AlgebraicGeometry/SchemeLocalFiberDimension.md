# Actual local fibre dimension and components

Worker 105 constructs the actual pointwise relative fibre dimension
used in Stacks Project Section 29.29, tag 02FW, and proves its comparison
with the componentwise pure dimension in Conrad's Theorem 3.4(2).
The registered sources are
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
and `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The component and pure-dimension comparisons are derived construction
properties, with the proof given below; they are not attributed to a
specific numbered assertion in either source.

For an actual scheme morphism `f : X ⟶ Y`, the definition
`relativeTopologicalKrullDimAt f x` applies `topologicalKrullDimAt` to
Mathlib's actual point `f.asFiber x` of the scheme-theoretic
residue-field fibre over `f x`. The canonical `fiberHomeo` identifies
this value with dimension at `x` of the set-theoretic fibre equipped
with its subspace topology. The same value is obtained from any actual
scheme-fibre point mapping to `x`. These statements need no finite-type
hypothesis. They realize the local dimension recalled at the beginning
of Stacks Section 29.29 using the neighbourhood minimum of Definition
5.10.1, tag 0055.

The preliminary topological arguments compute global dimension as the
supremum of component dimensions: restrict a finite chain of
irreducible closed sets to a component containing its largest member;
the reverse inequality is dimension monotonicity for subspaces.
If nonempty opens of components retain their dimension, equal component
dimensions imply the same dimension at every point. A minimizing open
neighbourhood meets a component through the point, so its dimension
bounds that component's dimension from above. Conversely, on a
Noetherian space a component contains a nonempty ambient open; the
dimension of that open is the supremum of its local dimensions.
Nonempty-open dimension invariance then determines the component's
dimension from the common local value.

For a scheme locally of finite type over a field, the existing
`componentOpenDimensionInvariant_locallyOfFiniteType` provides the
forward implication. For the converse, choose a point of a component
and an affine open containing it. Local finite type over a field makes
this chart Noetherian. The intersection of the component with the
chart is a component of the chart. Open-embedding invariance of local
dimension and the Noetherian comparison determine its dimension.
Nonempty-open dimension invariance and the homeomorphism between the
two orders of taking this intersection give the dimension of the
original component. Hence `HasPureDimension X d` is equivalent to
local dimension equal to `d` at every point of `X`. No quasi-compactness,
separation, reducedness, or nonemptiness hypothesis is imposed.
The empty scheme satisfies both conditions vacuously.

Applying this comparison to each actual residue-field fibre of a
locally finite-type morphism characterizes pure dimension of that
fibre by relative dimension equal to `d` at every source point above
its base point. Thus `HasPureDimensionFibers d f` is equivalent to
constancy of the constructed relative dimension on the source.
The combined nonempty, geometrically connected, pure-dimensional
condition is equivalently geometric connectedness of `f` together
with that constancy, by the existing exact fibre criterion.
The pure-dimension locus on the target is the complement of the image
of the actual source points whose relative dimension differs from `d`.
This equality includes empty fibres, which satisfy pure dimension
vacuously and have no source point of the exceptional image.

This unit does not prove openness or retrocompactness of relative
dimension sublevels, constructibility in a varying family, or filtered
descent of the combined fibre property. In particular, Stacks Lemmas
29.29.3, 29.29.4, and 29.29.6 are not claimed here.
