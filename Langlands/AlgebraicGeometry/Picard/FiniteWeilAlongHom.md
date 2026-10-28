# Finite Weil pairing along an actual dual-valued homomorphism

This internal construction pulls back the existing intrinsic finite Weil
pairing along an actual abelian-scheme homomorphism
`lam : A → dualAbelianSchemeFromEvaluation A ...`. In particular, it
constructs the finite pairing associated with every `lam` satisfying the
published `IsPolarization` predicate. The pullback construction itself
works for every such homomorphism, so it needs no ampleness or isogeny
proof as an extra argument.

The base is quasi-separated. The inputs retain the chosen actual dual
scheme, its explicit smooth, proper and geometrically connected
properties, the seven dual-constructor propositions, and an actual
inverse of the Poincare line bundle with tensor evaluation isomorphism.
The geometric properties equip this same dual group scheme with its
abelian-scheme structure. No arbitrary pairing or map on torsion points
is supplied.

For every natural number `n`, including zero,
`finiteWeilAlongHomTorsionMap` is the published
`Langlands.GroupScheme.Tate.kernelLevelMap (groupHom lam) n`, an actual
morphism of the multiplication kernels. The inclusion formula
`finiteWeilAlongHom_torsion_inclusion` identifies its composite with the
dual torsion inclusion with the primal torsion inclusion followed by
`lam`. It is thus the restriction of this particular homomorphism.
The source of the pairing is the actual product `A[n] ×_S A[n]`.

`finiteWeilAlongHomValue` evaluates `finiteWeilValue` on `x` and the
image of `y` under that torsion map. `finiteWeilAlongHomPairing` is the
product of the identity with that torsion map, followed by the published
scheme morphism `finiteWeilPairing`. Its point formula proves, for every
test scheme and every pair of torsion points,

```
e_n^lam(x, y) = e_n(x, lam(y)) = beta(lam(y))(x).
```

Here `lam(y)` means its actual restriction to `n`-torsion, and beta uses
the existing comparison between the dual multiplication kernel and dual
torsion. The order, normalization and roots-of-unity target are unchanged.
No roots of unity or Tate twist are trivialized.

`finiteWeilAlongHomValue_restrict` follows from associativity and the
existing test-scheme naturality of `finiteWeilValue`.
`finiteWeilAlongHomValueHom` is the original primal-variable evaluation
homomorphism at the image of `y`. It supplies identity and multiplication
preservation in that variable. The uniqueness theorem tests the proposed
point formula on the universal pair of projections. These proofs use
only the published constructions and their laws; this is their internal
provenance.

This unit asserts no second-variable group law, alternation, Cartier
duality, perfectness, nondegeneracy, transition compatibility, dual-map
functoriality, or inverse-limit pairing. Such conclusions require further
results about this constructed pairing. In particular it makes no claim
of integral perfectness for an arbitrary nonprincipal polarization.
