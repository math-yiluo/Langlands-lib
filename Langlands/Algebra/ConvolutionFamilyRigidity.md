# Natural convolution endomorphisms and coalgebra rigidity

This internal construction turns a family of endomorphisms of the convolution
monoids of algebra points into an actual coalgebra map. For a commutative
bialgebra `D` over a commutative ring `R`, the family is required to be natural
under every map of coefficient algebras. Its classifying algebra endomorphism
is its value on the universal point `id : D →ₐ[R] D`.

Naturality determines the whole family by precomposition with that map.
Preservation of the identity at the counit gives preservation of the counit.
The convolution of the two universal tensor inclusions is comultiplication,
using the published `TauCeti.Bialgebra.comulPoint_eq_include_mul` in reverse;
preservation of that convolution and naturality give preservation of
comultiplication. These two identities construct `EndFamily.coalgHom`.

The grouped theorem `EndFamily.app_eq_self_of_specialize` applies when
`D = R ⊗[k] C`, where `k` is a field, `R` is a commutative integral
`k`-algebra, and the group-like elements span the commutative `k`-bialgebra
`C`. Given a `k`-algebra map `ε : R →ₐ[k] k`, it assumes that specializing
the classifying map on `1 ⊗ c` gives `c`, for every `c : C`. Applying
`GroupLike.endomorphism_eq_id_of_specialize` to the constructed coalgebra map
then shows that every member of the family is the identity. All coefficient
algebras and the displayed rings lie in the same arbitrary universe.

This file is an internal derivation from naturality, the convolution
identities, and the integral scalar-extension rigidity theorem in
`Langlands.Algebra.GroupLikeDomainRigidity`.

This is an algebraic interface for actual families of group homomorphisms.
No family induced by a scheme action or centre-containment theorem is asserted
by this file alone.
