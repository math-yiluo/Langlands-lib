# Comparing a subgroup with an extension through their common quotient

This module gives an internal consequence of the actual fppf
kernel-quotient predicate and effective descent of scheme morphisms.

Let `q : H ⟶ Q` be an fppf quotient by the full represented image of `i : N ⟶ H`.
Let `j : M ⟶ H` be a monomorphism of group schemes, and suppose that `i` factors
as `a ≫ j` for `a : N ⟶ M`. If `j ≫ q` is flat, surjective and quasi-compact on
underlying schemes, `isoOfMonoContainingKernel` constructs an actual isomorphism
`M ≅ H` whose forward homomorphism is `j`.

For points on any test scheme, a point of `H` with the same quotient image as a
point of `M` differs from its image by a point of the actual kernel of `q`.
The full kernel-image equality in the fppf quotient predicate makes that
difference a point of `N`, hence a point of `M`. This proves
`factors_of_equal_quotient_images` without any monomorphism assumption.

Pulling `j ≫ q` back along `q` provides an fpqc cover of `H` and a local lift to
`M`. Monicity of `j` makes that lift agree on all pairs equalized by the cover.
Effective epimorphism descent produces a global inverse to the underlying
scheme map. Its two inverse identities give an isomorphism over the original
base, and the existing group structure lifts it to a group-scheme isomorphism.

The base scheme is arbitrary. There is no commutativity, affineness, finite-type
or smoothness hypothesis. This is the final subgroup-comparison step used in
the extension argument for groups of multiplicative type; it does not supply
the lifted subgroup or prove that the composite to the quotient is fpqc.
