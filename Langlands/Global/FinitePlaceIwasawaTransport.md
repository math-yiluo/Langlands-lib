# Transport of local Iwasawa compact data to actual finite-place points

Author: Worker 1624.

This internal construction transports the exact published
`CoordinateCompactPatching.IsLocalIwasawaCompact` predicate. It is derived
from the actual finite-completion point comparison and elementary
properties of continuous group equivalences. It introduces no external
structural assertion.

The generic theorem `IsLocalIwasawaCompact.map` uses a continuous
multiplicative equivalence `e : H ≃ₜ* H'`, group homomorphisms
`φ : Q →* H` and `φ' : Q' →* H'`, and any function `d : Q → Q'`
satisfying `e (φ q) = φ' (d q)` for every `q`. The four carrier universes
are independent. Neither source group needs a topology, and the ambient
groups need only the stated topologies.

Given a subgroup `K` satisfying the predicate for `φ`, its transported
subgroup is the literal subgroup image `K.map e.toMonoidHom`.
Compactness follows by taking the continuous image of `K`. For any
compact subgroup `L` containing that image, its inverse image under `e`
is compact by the homeomorphism and contains `K`. Unrestricted compact
maximality of `K` identifies this inverse image with `K`. Surjectivity of
`e` then proves `L = K.map e.toMonoidHom`.

For the product equality, take an arbitrary `g : H'` and decompose
`e.symm g` using the original literal equality
`Set.range φ * (K : Set H) = Set.univ`. Apply multiplicativity and the
commuting-square identity to obtain a factor in `Set.range φ'` on the
left and a factor in the transported compact subgroup on the right.
This proves the same literal pointwise set equality in `H'`. No
surjectivity or algebraic property of `d` is needed.

`FinitePlaceGroupPoints.baseChangeIwasawaCompact` specializes this
transport for every number field `F : Type u`, actual group scheme `G`
with affine underlying scheme, morphism `p : P ⟶ G`, and finite place
`v`. The source group is the identity-test rational points of the actual
base change of `G` to the actual `FiniteCompletion F v`; its topology is
exactly the named `rationalPointTopology`, bound only locally. The target
is the existing `FinitePlaceGroupPoints F G v` with its existing
regular-function evaluation topology.

The ambient equivalence is `baseChangeContinuousMulEquiv`. The function
on parabolic source points is the algebraic `baseChangeMulEquiv` for
`P`, and the commuting square is `baseChangeMulEquiv_map`. In
particular, no affineness or topology assumption on `P` is required by
this transport. The source homomorphism is `rationalPoints.map` of the
actual pullback of `p`. The target homomorphism is precisely the existing
`P.affinePointsTarget p` at the actual finite completion.

The construction is a function between subtypes of subgroups satisfying
these exact predicates. It therefore requires a supplied source
subgroup with compactness, maximality and product proofs. It proves no
existence of such a subgroup and does not close
`FinitePlaceGroupPoints.ParabolicIwasawaStatement`. Reductivity,
parabolicity and geometric existence remain separate prerequisites for
obtaining its input.
