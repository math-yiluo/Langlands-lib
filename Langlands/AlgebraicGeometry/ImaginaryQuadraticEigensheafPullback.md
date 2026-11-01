# Pullback of actual imaginary quadratic eigensheaves

This is a derived construction from the actual complementary quadratic
projectors and simultaneous scalar eigensubsheaves in
`ImaginaryQuadraticEigensheaf` and `ImaginaryQuadraticProjectors`. It supplies
the base change comparison needed for the positive Lie condition in
Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.89–90 (registered source
`harris-taylor-2001-geometry-cohomology-simple-shimura`). It is an internal
sheaf construction, rather than a theorem quoted from those pages.

Let L be an imaginary quadratic number field, K a characteristic-zero field
with an L-algebra structure, and b : T → S a morphism of schemes in one
universe. Both rings of global functions carry compatible K- and rational
algebra structures. The supplied K-algebra map c on global functions is
required to equal the actual ring map b.appTop. The sheaves M on S and N
on T carry actual L-actions. A map from b-pullback M to N must intertwine
every element of those actions.

Tensor induction proves that this map intertwines the tensor-algebra
actions after applying the actual coefficient map. The pure-tensor case
uses scalar semilinearity of module-sheaf pullback. Since the actual
quadratic idempotents commute with coefficient maps, the map also
intertwines the two sheaf projectors.

`sheafEigenPullbackMap` is the composite of the pulled-back source eigen
inclusion, the ambient map, and the target eigenprojection. The inclusion
and projection identities follow from projector intertwining and the
proved splitting identities. If the ambient map is an isomorphism,
`sheafEigenPullbackIso` has inverse given by the target inclusion, the
ambient inverse, and the pulled-back source eigenprojection. Both inverse
identities are proved by these same splitting identities and functor laws.

If a ring A acts on M and N, commuting with their L-actions, and the ambient
map intertwines A after pullback, `sheafEigenPullbackMap_intertwines` proves
that the constructed eigenmap intertwines the full restricted A-actions.
Its proof composes with the actual target eigeninclusion, uses its
monomorphism property, and applies the ambient intertwining equation.

Both choices of character are treated. There is no flatness, reducedness,
nonempty-base, finite-rank, or local-freeness assumption. The result does
not supply the ambient comparison for a particular Lie sheaf, the
positive Lie compatibility condition, or a moduli representability theorem.
