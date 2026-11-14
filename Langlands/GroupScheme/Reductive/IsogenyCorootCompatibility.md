# Scaled coroot compatibility in an fppf torus square

Author: Worker 659.

This internal unit extends the finite normalizer image argument of
`CentralIsogeny.CorootCompatibility` to a root pulled back to a positive
integer multiple of a source root. It is derived from the published actual
normalizer, fppf torus image, and lattice pairing interfaces. No additional
literature convention or geometric hypothesis is introduced.

The integral linear algebra lemma compares an automorphism `s` satisfying
`q s(y) = q y - f(y) x` with the reflection `t(y) = y - g(y) x`, where
`f(x) = 2q`, `g(x) = 2`, and `q` is a nonzero integer. Put `d = qg - f`
and `p = st`. Then `q p(y) = q y + d(y) x` and `d(p(y)) = d(y)`.
Induction gives `q p^n(y) = q y + n d(y) x`. A positive power of `p`
is the identity, so applying `g` gives `2n d(y) = 0` in the integers.
Thus `f = qg`. No torsion freeness of the ambient group is assumed.

The normalizer helper proves that the actual source automorphism and the
automorphism descended to an fppf torus image commute with the torus map.
It compares their composites with the closed target inclusion using
naturality of inner conjugation and then cancels that inclusion.

For the scaled coroot theorem, let `P` and `Q` be supplied actual root data
of `i : T → G` and `i' : T' → H` over any field. Both ambient groups are
affine. Assume that `T` is split, that the square with `φ : G → H` and
`t : T → T'` is an `IsFppfTorusImage`, that the underlying target inclusion
is a monomorphism, and that `weylImage i'` is finite. For any source and
target root indices `j` and `j'` and any natural number `q > 0`,
`IsRootDatumOf.coroot_comp_of_finite_weylImage_scaled` proves

```text
t ≫ Q.root j' = q • P.root j
  ⇒ P.coroot j ≫ t = q • Q.coroot j'.
```

The source root reflection has an actual normalizing point by the
published `IsRootDatumOf` normalizer theorem. Descending this point through
the fppf torus image gives a target torus automorphism. Its action on target
characters commutes with pullback, by the helper above and the inverse
automorphism identity. Pullback is injective because the torus map is flat
and surjective. The root equation therefore gives the scaled reflection
formula on the target character lattice, with functional given by pairing
with `P.coroot j ≫ t`. The actual target root reflection also comes from a
normalizing point. Both character automorphisms lie in the finite target
Weyl image, so their product has finite order. The integral lemma proves
equality of the first functional with `q` times pairing with `Q.coroot j'`.
The perfect pairing in `Q` then gives the asserted coroot equation.

The wrapper `IsRootDatumOf.coroot_comp_of_torusIsogeny_scaled` obtains the
fppf image and finite Weyl image premises from an actual torus isogeny,
splitness of both tori, a closed target torus inclusion, the commuting
square, and local finite type of `H`. An isogeny here means finite, flat,
and surjective. The existing split-torus finite-presentation theorem
provides the remaining fppf premise, and `splitTorusWeylImageFinite`
provides finiteness. Neither wrapper requires centrality or reductivity of
the ambient groups, nor any smoothness of the isogeny kernel.

The derived definition
`IsRootDatumOf.rootDatumIsogenyOfRootFactors` constructs
`RootDatumIsogeny p Q P`. In addition to the wrapper's hypotheses it
requires finite root index types, reduced root data, `p = 1` or `p` prime,
a supplied root index equivalence `e : J' ≃ J`, and natural root factors
`q j'` that are powers of `p` and satisfy the actual root pullback equations.
It uses the actual character pullback and actual cocharacter pushforward.
Injectivity follows respectively from flat surjectivity and finiteness of
the torus map. Compatibility with the pairings is associativity of
composition. The scaled coroot theorem supplies every required coroot
equation. Positivity of the powers follows from the assumption on `p`.
The specification theorem states that both lattice maps of this
constructed object are the actual maps; these identities are definitional.
The finiteness instances for the character and cocharacter lattices come
from splitness of the tori.

This unit supplies a conditional constructor and the scaled coroot
comparison, not the whole `IsogenyRootDatumStatement`. It does not construct
the root index equivalence or the characteristic-power root equations,
prove that a given ambient isogeny restricts to an isogeny of tori, or
establish the centrality and isomorphism comparison equivalences. Its
parameter `p` is assumed to be one or prime; identifying it with the
field's characteristic exponent belongs to the geometric application.
