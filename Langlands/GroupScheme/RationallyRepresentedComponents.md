# The finite group of rationally represented scheme components

Author: Worker 1107.

This is an internal derived construction from the published
`IdentityComponentRationalQuotient`, its transport and base-change modules, and
`IdentityComponentGaloisComparison`. The group structure is transported through
the published injective comparison with the ordinary rational-point quotient.
No external structure theorem is used.

Let `k : Type u` be any field and `H` an actual smooth affine group scheme over
`Spec k`, in the existing `Grp (Over (Spec k))` architecture.
`RationallyRepresentedComponents H` is the subtype
`Set.range (rationalComponentEmbedding H)` of the connected components of the
actual scheme `H.X.left`. A component lies in this subtype precisely when it
contains the underlying point of a rational section: the published quotient
projection is surjective and its embedding sends a projected section to its
`pointComponent`. The carrier is a subtype of actual scheme components.

`representedComponentEquiv` is the equivalence from
`RationalComponentQuotient H = H(k)/H^0(k)` onto this image supplied by
injectivity of `rationalComponentEmbedding`. Transport along its inverse defines
the `Group` instance, and `representedComponentMulEquiv` gives the resulting
group equivalence. The underlying component of the image of a quotient class
is exactly its published embedding, by `representedComponentMulEquiv_val`.
The inverse comparison has the corresponding embedding equation
`representedComponentMulEquiv_symm_embedding`. The group is finite by
injectivity into the published finite rational-component quotient.

`representedComponentOfPoint` is a homomorphism from actual rational sections
to this finite group. Its value in scheme components is `pointComponent`.
`representedComponentOfPoint_mul_val` identifies multiplication on represented
components with the component of the product of actual rational sections.
`representedComponent_one_val` identifies its identity with the component of
the identity section. Independence from representatives follows from the
group structure and equivalence with the published quotient.

For an actual homomorphism `f : H ⟶ H'` between smooth affine group schemes,
`representedComponentMap f` transports the published `rationalComponentMap`.
Its equation on quotient classes is `representedComponentMap_equiv`.
`representedComponentMap_val` proves that it is the restriction of the
continuous map on actual scheme connected components induced by `f`.
The identity and composition equations hold as homomorphism equalities.

Now let `L : Type u` be any field with a `k`-algebra structure, and write `H_L`
for `baseChanged k L H`. No algebraicity, separability, normality, perfection,
characteristic or Galois-extension hypothesis is imposed.
`representedComponentConjugate k L H sigma` transports the published
`rationalComponentConjugate` through the group equivalence. Its value on each
underlying scheme component is precisely
`coefficientComponents k L H sigma`, as proved by
`representedComponentConjugate_val` using the published actual-component
equivariance theorem. Thus these automorphisms restrict the actual semilinear
scheme-component permutations. Their one and multiplication laws give
`representedComponentGaloisAction`, a homomorphism
`Aut_k(L) →* MulAut (RationallyRepresentedComponents H_L)`.
`representedComponentConjugate_naturality` proves equivariance of maps induced
by actual homomorphisms over `k`.

`representedComponentFixedSubgroup` is the subgroup fixed by every coefficient
automorphism. `mem_representedComponentFixedSubgroup_iff` identifies this
condition with fixedness of the underlying actual scheme component under every
`coefficientComponents` permutation. `representedComponentFixedEquiv` is the
group equivalence from the published `rationalComponentFixedSubgroup` to this
subgroup; its inverse is the restriction of the inverse quotient comparison.
`representedComponentBaseChangeToFixed` is an injective homomorphism from the
represented components over `k` to this fixed subgroup over `L`. The
`representedComponentBaseChangeToFixed_val` equation identifies its underlying
actual component with the published field-extension map on rational quotient
classes. These constructions use the existing injectivity and fixedness of that
field-extension map.

The group is constructed on the rationally represented components only. This
module does not assert that every scheme component has a rational point, even
when the field is algebraically closed. It constructs no group scheme or sheaf
quotient, no descent of arbitrary fixed components or fixed quotient classes,
no surjectivity onto the fixed subgroup, and no topology or continuity result
for the coefficient action. The ordinary quotient used throughout is the
quotient of rational-point groups.
