# Naturality of actual stalk algebras

This internal adapter concerns an arbitrary morphism `f : X ⟶ Y` over a field
`K`, with structural morphisms `p` and `q` satisfying `f ≫ q = p`. The field
and both schemes lie in an arbitrary common universe. There are no finiteness
or algebraic-closure hypotheses.

The canonical `K`-algebra structure on each actual structure-sheaf stalk is
`Picard.stalkAlgebraOver`. The construction `stalkMapAlgHomOver` makes
Mathlib's actual `f.stalkMap z` into a homomorphism of these algebras.
Its underlying ring homomorphism is exactly the original stalk map.
To construct it, fully faithful `Spec` converts the equation
`Spec(f.stalkMap z) ≫ Y.fromSpecStalk (f z) = X.fromSpecStalk z ≫ f`,
together with the equation over the base, into the scalar compatibility.

For a rational point `x` of `X`, its image `x ≫ f` is rational over `K`.
Precomposing the canonical augmentation at `x` with this stalk algebra map
gives the canonical augmentation at `x ≫ f`. This is the algebra-homomorphism
form of Mathlib's `Scheme.stalkClosedPointTo_comp`.

The final identity records compatibility with actual tangent morphisms:
precomposing any dual-number algebra map on the source stalk with the
stalk algebra map, then taking its spectrum and the canonical map to `Y`,
agrees with its spectrum followed by the canonical map to `X` and `f`.
This identity concerns the displayed maps themselves, without requiring an
additional factorization certificate.

All assertions are direct consequences of Mathlib's stalk identities and the
canonical algebra construction in `StalkTangent`. No external theorem is
transcribed. This module does not assert cotangent surjectivity or a local
closed-immersion criterion.
