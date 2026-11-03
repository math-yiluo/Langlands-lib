# Polynomial comparison with a closed algebraic embedding height

`Langlands.Global.RepresentationGrowth.ClosedImmersionHeightDominationStatement`
is a proposition specifying a structural comparison for the existing actual
representation heights. This file states the comparison; it contains no proof
of that proposition.

For every number field `F`, every actual group scheme `G` over `Spec F`,
all natural ranks `N` and `M`, and actual group-scheme homomorphisms

```text
rho   : G -> GL_N,
sigma : G -> GL_M,
```

assume `GroupScheme.IsClosedSubgroup rho`. This is the published predicate
`IsClosedImmersion rho.hom.hom.left` for the underlying scheme morphism.
The conclusion is that there are a real `C >= 1` and a natural `d` such that,
for every `g : InfiniteAdelicGroupPoints F G`,

```text
height F G sigma g <= C * (height F G rho g)^d.
```

The witnesses may depend on `F`, `G`, both ranks and both representations;
they must work simultaneously for all infinite adelic points. There is no
faithfulness requirement on `sigma`. Both ranks may be zero. No separate
smoothness, connectedness or reductivity premise occurs in the statement.
The closed immersion into the affine general linear group is the algebraic
hypothesis used for the coordinate comparison; pointwise injectivity is not
substituted for it.

The height is exactly the existing `RepresentationGrowth.height`: evaluate the
specified algebraic representation on the actual infinite adele ring, use the
published general linear point comparison, and apply the original
`ArchimedeanGL.matrixHeight`. The latter is `max 1` of the matrix norm and the
inverse-matrix norm after applying `archimedeanGLCoordinates`. Its coefficient
ring is the mixed real and complex space, with its product Banach algebra norm,
and its matrix norm is the supremum of the row sums of coefficient norms.
No height or norm is redefined here.

The source motivation is Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), equations (6.3) and (6.4), printed pages 158–159,
the paragraph following Definition 6.2.1 on page 159, and Exercise 6.1 on
pages 179–180. The source doubles a closed embedding with the inverse
transpose, uses products of local entry suprema, and asks for polynomial
comparison between two faithful representations of a reductive group over a
global field. The present proposition is an internally derived coordinate
comparison for the Library's fixed mixed-space height, over number fields,
with a closed embedding on the controlling side and an arbitrary algebraic
representation on the other side. It is not a literal transcription of the
exercise, and no equality with the source's product norm is asserted. The
registered October 2026 five-page author errata contain no correction to
these passages or Exercise 6.1.

The intended derivation uses the existing coordinate presentation of `GL_N`
by matrix and inverse-matrix variables. A closed immersion with affine target
is surjective on global regular functions. Pull back a matrix coordinate of
`sigma` to `G`, lift it through that surjection to a regular function on
`GL_N`, and represent the lift by a polynomial in the matrix and inverse
variables. Evaluate in mixed coordinates. Each variable is bounded by the
controlling height, and every fixed polynomial has a bound by a constant
times a natural power of that height. There are finitely many output matrix
coordinates, so finite sums and maxima produce a matrix-norm bound. Inversion
compatibility supplies the inverse-matrix bound. Enlarging the resulting
constant to at least one also controls the outer `max 1`. This paragraph
explains the provenance and proposed route; the Lean file does not implement
that derivation.

Two closed-immersion representations would yield bounds in both directions.
Those bounds would imply equality of their existing polynomial-growth
predicates and function submodules by substituting the bounds in the growth
inequality. They would also give equality of the corresponding adelic
slice-growth spaces. These are subsequent consequences, not declarations
proved in this file. In particular, this statement alone does not discharge
representation independence, global adelic growth, uniform differential
growth, reduction theory, finite volume or any Hilbert realization.
