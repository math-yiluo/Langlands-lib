# Geometry of the diagonal kernel of a triangular subgroup

`Langlands.GroupScheme.TriangularDiagonalKernelGeometryStatement.{u}` is a
proposition target. This module supplies no proof.

For every algebraically closed field `k : Type u`, let `H` be a group scheme
over `Spec (CommRingCat.of k)` satisfying `Smooth H.X.hom`,
`IsAffineHom H.X.hom` and `ConnectedSpace H.X.left`. For every natural number
`N` and homomorphism

```text
j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
          (fun i => -(i.val : ℤ))
```

satisfying `IsClosedSubgroup j`, set

```text
f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
           (fun i => -(i.val : ℤ)).
```

The conclusion is exactly
`Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left`.
There is no hypothesis of smoothness or connectedness of the kernel, and no
splitting hypothesis. The universe `u` is arbitrary and `N` may be zero.

## The concrete map and kernel

Write `e i = -(i.val : ℤ)`. The existing block parabolic scheme has matrix
entries zero when `e i < e j`, which for these weights means `i.val > j.val`.
It is thus the upper triangular group `T_N` in Milne's notation. Distinct
indices have distinct weights, so the block Levi scheme is the diagonal
group `D_N`. The existing theorem
`GeneralLinear.pointsEquiv_blockLimitHom` identifies `blockLimitHom` with
the block diagonal projection on every test scheme. For these weights it is
the ordinary diagonal map `T_N → D_N`.

The kernel in the statement is literally `Langlands.GroupScheme.kernel f`,
the pullback of `f` along the target's identity section. The existing
`kernelPointsEquiv` identifies its points on every scheme over `Spec k`
with the points of `H` killed by `f`. Consequently it is the
scheme-theoretic intersection of `H`, embedded by `j`, with the upper
unitriangular group `U_N`: its diagonal entries are all one. Equivalently,
it is the pullback to `H` of the ambient kernel, which is identified with
the existing block unipotent scheme by
`GeneralLinear.blockUnipotentIsoKernel`. This description retains
nonreduced test schemes; it does not replace the kernel by its reduced
subscheme or identity component.

## Literature correspondence

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (2017), Chapter 16:

- Proposition 16.2(c)⇒(d), printed p.325 (one-based PDF page 341), takes a
  closed subgroup `G` of `T_N` and sets `U = U_N ∩ G`. It shows that `U`
  is normal and unipotent and that `G/U` is diagonalizable.
- Theorem 16.6 and Note 16.8, printed pp.325–326 (one-based PDF pages
  341–342), identify this subgroup with the canonical `G_u`: a normal
  unipotent subgroup whose quotient is of multiplicative type. Apply
  this identification to `G = H` and the actual intersection above.
- Note 16.10, printed p.326 (one-based PDF page 342), states that `G_u`
  is smooth when `G` is smooth, and connected when `G` is connected.
  It invokes Theorem 16.26(a), printed pp.332–333 (one-based PDF pages
  348–349), which gives a splitting over an algebraically closed field.
  That splitting is a source theorem used to obtain the conclusion,
  rather than an extra premise of this target.

This statement isolates precisely the smoothness and connectedness
conclusions of 16.10 for the given diagonal kernel. It does not state an
existence or maximality theorem for unipotent subgroups.

Milne's algebraic groups are affine group schemes of finite type over the
field. Here smoothness makes `H → Spec k` locally of finite presentation,
hence locally of finite type; affineness makes it quasi-compact. Therefore
`H` is of finite type without an additional hypothesis. The diagonal
target is affine and hence separated, so its identity section is closed.
Its pullback, the actual kernel, is closed in `H`, and is therefore also
affine and of finite type. This explains the finite-type correspondence
without assuming the asserted kernel geometry.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. It has no
correction to 16.2, 16.6, 16.8, 16.10 or 16.26.

Book source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
