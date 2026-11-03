# The actual origin of the affine line

This is construction infrastructure for the paragraph immediately after
Proposition 2.1 on printed page 2 of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
That paragraph tests closedness of point images on the origin in the affine
line. The construction here also permits a separate base ring and value
algebra; the paper's setting is recovered by taking both to be the same ring.

Let R and S be arbitrary commutative rings in the common scheme universe,
and let S be an R-algebra. No topology on R is used.
`affineLineOrigin R` is the actual morphism over Spec R from Spec R to
Spec R[t], with the polynomial algebra modeled by `MvPolynomial Unit R`.
It is induced by evaluation of the coordinate at zero. Evaluation is
surjective because every constant polynomial evaluates to its constant,
so the morphism is a closed immersion. These constructions and laws allow
the zero ring and nonfaithful algebra structures.

`affineLinePointEquiv R S` identifies actual morphisms from Spec S over
Spec R to this affine line with elements of S, by evaluation of the
coordinate. Its inverse is the polynomial evaluation algebra map transported
through the existing actual spectrum-point equivalence. The inverse laws
use uniqueness of an algebra map out of a polynomial algebra from its
values on the variable.

`affineLinePointEquiv_origin` identifies the composite of any actual
S-point of Spec R with the origin: its coordinate is zero.
`range_affineLineOrigin_points` says that the image of this actual map
on points is exactly the inverse image of the singleton zero under the
coordinate equivalence. The reverse inclusion uses the canonical
S-point of Spec R and injectivity of the coordinate equivalence. No
closedness or Hausdorffness is asserted by this algebraic range law.

For any topology making S a topological ring,
`affineLinePointHomeomorph R S` gives this same coordinate function as a
homeomorphism. Its domain has the previously constructed global-section
evaluation topology, and its codomain has the given topology on S.
The implementation composes the existing spectrum-point homeomorphism,
polynomial-point homeomorphism and evaluation homeomorphism for a
one-element index type. This is a derived specialization of the
published affine topology construction, not a topology defined by a
desired closedness property.

The necessity of Hausdorffness and the criterion for all closed
immersions to induce closed embeddings are separate proposition targets.
