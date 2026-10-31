# Natural filtrations after a quotient by an initial step

This internal construction maps a natural filtration to a quotient functor.
It is intended for restricting a support filtration to a closed union of
orbits. It assumes the actual natural quotient map, its objectwise
surjectivity, and its exact kernel; it constructs no geometric restriction
map or inner-Levi comparison.

`RepSubfunctor.directImage` takes the actual image of each invariant
submodule under a natural transformation. Its restricted natural map is
surjective onto this image. `directImageQuotientIso` identifies the original
quotient of two steps with the quotient of their images when the ambient
kernel is contained in the lower step. The map sends the class of a vector
to the class of its image. Its kernel calculation subtracts a representative
in the lower step, and its surjectivity lifts through the image and quotient
projections. The existing natural first-isomorphism constructor packages
these calculations into a natural isomorphism.

For a filtration of length `a + b`, `RepFunctorFiltration.quotientTail`
takes the images of steps `a, ..., a + b`. The supplied kernel equality
makes the first image zero, and the supplied surjectivity makes the last
image the entire target. Every successive quotient is naturally isomorphic
to the original quotient at the corresponding index. Consequently its
graded functors are exactly the final `b` graded functors of the original
filtration.

The construction works over a commutative ring for representations of a
monoid and arbitrary source category, with independent universes. Its
provenance is the elementary image and quotient universal properties and
the published `Filtration.Definitions` and `Filtration.QuotientFirstIso`.
It makes no new claim about the literature and does not prove a geometric
lemma.
