# Scheme charts of relative diagonals

This internal construction associates two actual schemes to a scheme chart
`a : h_U → X` and a morphism `f : X → Y` of algebraic spaces: the kernel pair of
`a` and the kernel pair of `a ≫ f`. Representability of the absolute diagonals
of `X` and `Y` supplies both schemes. The induced map between them is a
represented pullback of the relative diagonal of `f`.

The target kernel pair is an étale, respectively surjective, chart of
`X ×_Y X` when `a` is étale, respectively surjective. Thus any scheme property
stable under base change and descending along surjective étale scheme maps
tests the relative diagonal on this one comparison map. For closed
immersions, the scheme descent theorem in `SchemeFlatPropertyDescent` gives
the separatedness criterion.

The proofs use the pullback universal properties. Representability of the
relative diagonal follows by cancellation of the monomorphism
`X ×_Y X → X ×_S X` from the representable absolute diagonal. No finiteness
condition or limit theorem is asserted here.
