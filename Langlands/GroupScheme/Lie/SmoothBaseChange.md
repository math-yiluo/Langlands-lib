# Canonical Lie-sheaf base change for smooth group schemes

For any smooth group scheme `G` over an arbitrary scheme `S` and any
scheme morphism `b : T → S`, `GroupScheme.smoothLieBaseChangeIso b G hG`
constructs an actual module-sheaf isomorphism

```
b* G.Lie ≅ ((GroupScheme.baseChange b).obj G).Lie.
```

Here `G.Lie` is the existing internal sheaf dual of the cotangent sheaf
at the actual identity section. The group need not be affine,
commutative, connected or proper. The base and its morphism need no
additional hypotheses, and the construction works in every scheme
universe `u`.

The existing cotangent base-change map is invertible for every group
scheme. Smoothness supplies finite local bases of the cotangent sheaf
at the identity, so the existing canonical dual-pullback comparison is
also invertible. The constructed isomorphism composes that comparison
with the inverse of the dual of the cotangent base-change map.

`smoothLieBaseChangeIso_characterization` says that postcomposing the
forward map with the dual cotangent comparison gives precisely the
canonical dual-pullback comparison. This equation determines the
isomorphism, as proved by `smoothLieBaseChangeIso_unique` by cancellation
of the invertible dual cotangent map.

`smoothLieBaseChangeIso_naturality` proves the square for every actual
group-scheme homomorphism `f : G → H` between smooth groups. It compares
pullback of `lieMap f` with the Lie map of the actual base-changed
homomorphism. The proof dualizes the published cotangent naturality
square, cancels the target's invertible dual cotangent map, applies the
characterization to both groups and finishes with naturality of
`dualPullbackComparison`.

This is internal derived content. It extends the construction already
implemented for abelian schemes in `AbelianScheme/LieBaseChangeProof`
to arbitrary smooth group schemes, using the published arbitrary-group
cotangent isomorphism and naturality and the smooth finite local frames.
It constructs no new differential or Lie bracket and does not assert
identity or composition coherence in the base morphism; those laws
require their own proof.
