# Actual augmentation cotangents

This derived construction implements the augmentation cotangent in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §3.3,
printed p.107 / PDF p.133. It imports the actual coordinate action rather than
introducing an abstract representation. The construction is uniform in universe
and field characteristic, and does not require splitness or smoothness.

`Cotangent G` is Mathlib's actual quotient `I/I²` for
`I = ker (Lie.coordinateOrigin G)`. `cotangentMk` is its scalar-restricted
quotient map. After arbitrary coefficient extension, `baseAugmentation` evaluates
at the actual identity point, and `BaseCotangent` is the cotangent of its kernel
in `A ⊗ O(G)`. `cotangentBaseChange` is induced by `f ↦ 1 ⊗ f`; no assertion
that it becomes a tensor-product isomorphism is assumed.

`baseAugmentation_action` proves equality of the full tensor augmentation before
and after action pullback, by evaluating pure tensors at the identity.
This proves stability of its kernel and gives `cotangentAction`, the induced
`A`-linear map on `I_A/I_A²` through `Ideal.mapCotangent`.
`IsCotangentEigenvector` and `cotangentWeightSpace` use this map after every
commutative coefficient algebra and every torus point. The character value is
used directly, with no inverse character. `cotangentSupport` means a nonzero
vector in such an eigenspace and allows the zero character when present.

The comparison with the existing actual Lie kernel and its intrinsic eigenvectors
requires a separate proposition target. In particular this module does not
identify dual weights by the usual contragredient convention: CGP uses pullback
on functions, giving the same labels on cotangent and tangent supports.
