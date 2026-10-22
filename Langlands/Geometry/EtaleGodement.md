# Scheme etale specialization of the Godement construction

Author: Worker 13.

For an actual Mathlib scheme `X`, this module uses Mathlib's small etale site:
objects are schemes etale over `X`, and coverings are jointly surjective etale
families. At each point `x` of `X`, the separable closure of its residue field
gives a morphism `Spec (SeparableClosure κ(x)) → X` and the associated site
point. The conservativity of this family is obtained from Mathlib's proved
`Scheme.isConservativeFamilyOfPoints_pointSmallEtale'`.

For a commutative coefficient ring `R`, `EtaleSheaf X R` is the existing
category of `ModuleCat R`-valued sheaves on that site, including its genuine
natural-transformation morphisms. Applying the accompanying Godement
construction gives the product-of-skyscrapers functor, its canonical
coaugmentation, and all terms and maps of the nonnegative cochain complex.
Conservativity of the actual geometric points supplies joint faithfulness of
the fiber functors, and the general adjunction argument proves that the
canonical coaugmentation is a monomorphism for every module-valued etale sheaf.
No scheme, site, stalk, differential or cohomology group is supplied as an
unconstrained placeholder.

The module proves that forgetting module structure preserves the sheaf
condition on this site. Evaluation at `1` identifies the underlying-set
functor with the functor corepresented by the free rank-one module `R`.
Consequently the module-valued sheaf condition implies the set-valued sheaf
condition after forgetting. This explicit argument avoids imposing larger
limit universes on the coefficient category. Mathlib's conservativity theorem
then applies to these concrete module-valued sheaves.

This is an algebraic etale specialization of the general site construction.
It is not a construction of the analytic equivariant site of Berkovich, a
Shimura variety, a Drinfeld uniformization, or a comparison between those
objects. Those specializations remain explicit obligations of the Harris
branch. Nor does this module assert compact-support acyclicity or identify its
complex with derived compact-support cohomology.

The construction follows the point-family and cokernel recipe in Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces*, section 1.5, printed/PDF
page 10, as a stated derived generalization to scheme etale sites. Worker 13
read that original passage. The source is the supplied unfinished 1995–1996
manuscript, registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The actual scheme and etale point construction is reused from pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`, especially
`AlgebraicGeometry.Sites.EtalePoint`. Its intrinsic obligations, including the
cover-lifting property of each geometric fiber, are already proved there.
The scheme's underlying space, residue fields, coefficient ring and module
carriers live in universe `u`. The category of small-etale objects and the
category of modules have object universe `u + 1`; their morphisms live in
universe `u`. Sheaves and their morphisms use the universes determined by
these categories. No project axiom,
finite-dimensionality assumption or torsion restriction is introduced.
