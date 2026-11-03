# Actual Lie actions and determinant characters under base change

Let `k` and `K` be commutative rings in any common universe `u`, with a
`k`-algebra structure on `K`. Let `a : AutomorphicAction H U` be an actual
automorphic action over `Spec k`, and write `H_K`, `U_K`, and `a_K` for their
scheme pullbacks along `algebraBaseMap k K`. This is an internal, derived
construction from the action pullback, the actual Lie-kernel comparison, and
the finite-coordinate determinant construction; no external structural
theorem is used.

For every commutative `K`-algebra `A` with a compatible `k`-algebra structure,
`affineBaseChangeEquiv_act` proves that the published multiplicative
comparison of actual affine points intertwines `a_K` and `a`.
`kernelBaseChangeEquiv_action` combines this identity with compatibility of
constant dual-number points to identify the actions on the identity
kernels. These two comparisons impose no affineness hypothesis.

If the structure morphism of `U` is affine, its published linear kernel
comparison intertwines the actual differentials
(`differential_baseChange`). Consequently these linear automorphisms have
the same determinant (`differential_det_baseChange`). The implemented
proof identifies one differential as the conjugate of the other and
applies invariance of the determinant under a linear equivalence.

`Lie.FiniteCoordinates.baseChange` transports natural finite coordinates
of rank `d` on `U` to natural finite coordinates of the same rank on
`U_K`. At a `K`-algebra `A`, it first uses the actual linear kernel
comparison and then the original coordinates on `A`, regarded as a
`k`-algebra through `K`. Its naturality follows from the naturality of
both comparisons under every coefficient-algebra map. Neither the
action nor a determinant character is supplied as part of these
coordinates.

`rationalCharacters.characterEval_baseChange_affine` identifies the
value of an actual pulled-back rational character with its original
value under the affine point comparison. The proof uses the all-test
character pullback formula and the canonical isomorphism of the two
affine test schemes, whose underlying scheme map is the identity.

Assume in addition that `H` is affine, and choose natural finite
coordinates `c` for `U` and `cK` for `U_K`. The ranks and choices may be
arbitrary. `determinantCharacter_baseChange_eval_affine` combines the
character evaluation comparison with the two actual Lie determinant
evaluation formulas and the conjugacy result. Both section-valued
formulas use the same underlying global-sections/spectrum isomorphism.
`determinantCharacter_baseChange` then proves the equality of actual
rational characters

```text
rationalCharacters.baseChange (algebraBaseMap k K) (a.determinantCharacter c)
  = (a.baseChange (algebraBaseMap k K)).determinantCharacter cK.
```

For the last step the implemented proof presents the affine source
`H_K` as the relative spectrum of an algebra, proves equality on its
universal affine point, and transports that equality to every test by
naturality. Thus the conclusion is an equality of the actual character
morphisms, with no restriction to rational points. Compatible `cK` always
exists by the finite-coordinate construction above when `c` is given.
The unit requires no field, flatness, separability, smoothness, splitness,
or geometric positivity assumption. It does not construct a maximal
split torus or prove a Levi-centralizer theorem.
