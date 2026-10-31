# Center orbits as images of an annihilating center quotient

Author: Worker 94.

This internal linear-algebra construction uses the published actual
archimedean enveloping center, its complex-linear orbit map and its action
on genuine smooth functions. The number-field universe and natural rank
are unrestricted. No external theorem is attributed to this pair.

Given a center ideal `I` and a smooth function `f` annihilated by every
element of `I`, `centerQuotientOrbitMap I f hf` descends the published
`centerOrbitMap f` through the complex subspace `I.restrictScalars ℂ`.
It maps the class of `z` to the actual smooth function `centerAction z f`.
The annihilation hypothesis is exactly the kernel containment required
by the quotient's linear universal property.

`centerQuotientOrbitMap_range` identifies its range with the published
`centerOrbitSpan f`: the quotient projection is surjective, so descent
does not change the range of the orbit map.
`isCenterFinite_of_finite_quotient_annihilates` then proves center
finiteness whenever this quotient is finite-dimensional over the complex
numbers. It uses finite-dimensionality of the range of a linear map
from a finite-dimensional space.

The conclusion is finiteness of the center orbit of this specified
function. A common ideal can apply the same result to every vector it
annihilates, but this pair asserts no finite multiplicity of compact
types. Finite central generation, admissibility, closure transfer,
convolution reproduction and automorphic differential growth require
separate arguments.
