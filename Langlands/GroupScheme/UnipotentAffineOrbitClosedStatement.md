# Closed unipotent orbits on affine algebraic schemes

Worker 1460.

`Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement.{u}` is a
proposition definition for the Kostant–Rosenlicht theorem, Milne,
*Algebraic Groups* (2017), Theorem 17.64, printed pp.373–374
(one-based PDF pp.389–390). This module states a proof target and supplies
no proof.

Fix an algebraically closed field `k : Type u`, with no restriction on
its characteristic, and write `S = Spec (CommRingCat.of k)`. The group
`U : GroupScheme S` is smooth and affine over `S` and satisfies the
published `IsUnipotent U`. Smoothness gives local finite type and
affineness gives quasi-compactness, so `U` is a group variety of finite
type, as in the source. Connectedness is not assumed. The existing
unipotence predicate says that every nonzero finite-dimensional
representation has a nonzero vector fixed on every test scheme; this is
the representation-theoretic meaning of unipotence used in the source
proof, with the existing matrix-representation convention.

The acted-on scheme is an actual `X : Over S`, with `IsAffine X.left`
and `LocallyOfFiniteType X.hom`. Since the base and `X.left` are affine,
the structure morphism is affine and quasi-compact; local finite type
therefore retains finite type. The scheme is separated over the field.
These are the affine algebraic schemes of the source. No reducedness,
smoothness, irreducibility or connectedness is imposed on `X`.

For an actual categorical action `a : SchemeAction U X` and a rational
section `x : 𝟙_ (Over S) ⟶ X`, the expression

```lean
a.act (𝟙 U.X) (toUnit U.X ≫ x) : U.X ⟶ X
```

is the orbit morphism, obtained by acting on `x` with the universal group
point. The conclusion says that the range of its underlying scheme map
is closed in the Zariski topology of `X.left`. It includes all points of
the underlying group scheme in that image, rather than equipping a set
of rational points with an unspecified topology. Over an algebraically
closed field, this range is the underlying subset of the geometric
orbit of the rational point. The statement restricts the source theorem
to such orbits, which suffices for the flag-step consumer.

The source proof first replaces `X` by the closure of an orbit. The
reduced boundary is stable; its coordinate ideal is nonzero if the
boundary is nonempty. Unipotence supplies a nonzero invariant function
in this ideal. That function is constant on the dense orbit and hence
on its closure, forcing the boundary to be empty. These steps describe
the literature proof, not a Lean implementation. Passing from the
published finite-dimensional fixed-vector predicate to coordinate
ideals, invariant reduced boundaries and orbit images remains part of
the separate proof obligation.

The only Lean imports are already published definitions and morphism
infrastructure. In particular, this target does not assume a closed-orbit
result, a quotient, a fixed point or an invariant affine cover.

The registered source is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no correction to Theorem 17.64.
