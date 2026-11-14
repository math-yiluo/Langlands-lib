# Actual inverse image of Deligne's flat graded and framed lattices

This module constructs ordinary inverse image of the actual lattice eta and
rational frame r used in Drinfeld's description of Deligne's formal space.
It is a derived construction toward Task 5556, item 4.

The original source is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed p.109 (PDF p.3), final paragraph defining
eta,T,u,r, continuing on printed p.110 (PDF p.4), conditions (a)-(c).
Section 2 B, Proposition 2.4, printed p.110 (PDF p.4), asserts inverse-image
compatibility of all four data associated to a special formal module.
The registered literature identifier is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, with content SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions here supply the lattice and frame part of the inverse-image
infrastructure; they do not prove Proposition 2.4.

## Scope and coefficient conventions

All coefficient rings and spaces use a common universe. The generic
inverse-image constructions require a commutative coefficient ring O and a
continuous map f : X -> Y. The lattice constructions use the actual quotient
algebra `PiAlgebra d pi` = O[Pi]/(Pi^d-pi), the actual module sheaves from
`DeligneLatticeSheaf`, and, for the finite-sum and object constructions,
positive d, expressed by `NeZero d`. The frame construction additionally
uses an O-algebra field F. No fraction-field, valuation, nonzero pi or
nilpotence hypothesis is needed for these comparisons. They can therefore
be specialized to the source's situation.

The inverse image is Mathlib's actual `TopCat.Sheaf.pullback`. It is the
ordinary topological inverse image with the same coefficient ring, rather
than structural-module pullback along a scheme morphism. The latter
operation changes the structure-sheaf scalars and is distinct infrastructure.

## Stalks, additivity and coefficient multiplication

`inverseImageStalkIso f M x` identifies the original M stalk at f(x) with
the stalk of the actual inverse-image sheaf at x. Its construction composes
three isomorphisms: the presheaf inverse-image stalk isomorphism, the stalk
isomorphism of sheafification, and the inverse of the stalk map of
`TopCat.Sheaf.pullbackIso`. Thus it identifies the actual module structures
on the stalks, and not just their underlying sets.

`inverseImage_preservesFiniteLimits` instantiates Mathlib's finite-limit
preservation theorem for this module-sheaf inverse image.
`inverseImage_additive` follows from preservation of binary products.
These instances allow transport of the finite splitting equations below.

`coefficientMultiplication M a` is multiplication by the actual coefficient
a on every module of sections. Its restriction naturality is precisely
linearity of the restriction maps. `inverseImage_smul` proves that its
inverse image is coefficient multiplication by the same a. Apply the
inverse-image/direct-image adjunction and test equality after its hom-set
bijection; the remaining equation is linearity of the adjunction unit.

`inverseImageLatticeScalarIso` specializes the restriction-of-scalars
comparison from `DeligneSheafBaseChange` to O -> O[Pi].
`inverseImage_latticePiIntegral` specializes preservation of coefficient
multiplication to the actual distinguished element Pi. Naturality of the
restriction comparison then proves `inverseImageLatticeScalarIso_pi`,
which identifies the two actual Pi actions after restricting to O.

## Canonical homogeneous projections and the internal sum

For an existing `LatticePiSheaf`, `sectionProjection U i` first applies the
inverse of the bijective internal-sum map on U, selects its i-th range
component, and uses the inverse of the injective homogeneous inclusion
onto that range. The diagonal and off-diagonal inclusion identities follow
from the existing internal-sum inverse identities.

`section_hom_ext` tests linear maps on homogeneous inclusions: surjectivity
of the internal-sum map and induction on the direct sum reduce every section
to homogeneous sections. This test proves that `sectionProjection` commutes
with restrictions, so `projection i` is a genuine O-module sheaf map.
`inclusion_projection`, `inclusion_projection_ne` and
`sum_projection_inclusion` give the orthogonal splitting and the finite
sum of projection followed by inclusion equal to the identity. For the last
equation, test on homogeneous sections and evaluate the sum using the
diagonal and off-diagonal equations.

The generic auxiliary lemma `isInternal_of_finite_splitting` works for any
finite index type over O. Given inclusions a_i and projections p_i with
p_i a_i = id, p_i a_j = 0 for j distinct from i, and sum_i a_i p_i = id,
it proves internality of the actual ranges of a_i. Induction on a direct
sum recovers each range coordinate from its image in the total module;
this proves injectivity. The sum identity gives a preimage of every total
element, proving surjectivity. This lemma is internal linear-algebra
infrastructure derived from the definition of an internal direct sum.

## Actual lattice inverse image

`LatticePiSheaf.inverseImageInclusion` is inverse image of the original
inclusion followed by the coefficient restriction comparison.
`inverseImageProjection` uses its inverse and inverse image of the original
projection. Functoriality transports both orthogonality equations.
Additivity transports the finite sum identity. Evaluating these identities
on actual sections and applying `isInternal_of_finite_splitting` proves
`inverseImage_isInternal` on every open of X.

`LatticePiSheaf.inverseImage M f` has the following actual data:

- Total sheaf: inverse image of M.sheaf as an O[Pi]-module sheaf.
- Components: ordinary inverse images of the O-module component sheaves.
- Inclusions: the compared inverse-image inclusions just constructed.
- Pi component maps: inverse images of the original component maps.

Flatness over O[Pi] at x follows from the original flatness at f(x) using
`inverseImageStalkIso` and `Module.Flat.equiv_iff`. Each inclusion is
injective on sections because its pulled projection is a left inverse.
The ranges give an internal direct sum by the finite splitting argument.
The Pi inclusion square follows from the original square, functoriality,
and `inverseImageLatticeScalarIso_pi`. No splitting, flatness certificate
or operator square is supplied as additional input.

## Actual rational frame inverse image and remaining work

`FramedLatticePiSheaf.inverseImage M f` uses that constructed lattice. Its
frame is the composite of the inverse constant-sheaf comparison, inverse
image of M.frame as an F-sheaf isomorphism, and the rationalization
comparison on the original degree-zero component. The target is the
actual rationalized degree-zero component of the constructed lattice.
Both comparisons were constructed from the actual adjunctions in
`DeligneSheafBaseChange`; no replacement frame is assumed.

This unit constructs the lattice and framed lattice on objects. It does
not construct a functor on their morphism categories or prove identity and
composition comparison laws. It does not assemble structural line-sheaf
pullback, local generation or full eta,T,u,r base change, transport
admissibility, construct the Nilp functor or normalized PGL action, prove
existence or representability, or identify these data with those attached
to a special formal module. The previously documented stalkwise determinant
comparison boundary remains. Those are further obligations of the host task.
