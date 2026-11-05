# Geometry of the actual diagonal kernel of a triangular subgroup

`Langlands.GroupScheme.triangularDiagonalKernelGeometry` proves exactly
`Langlands.GroupScheme.TriangularDiagonalKernelGeometryStatement.{u}` at arbitrary
universe `u`. For every algebraically closed field `k : Type u`, smooth connected
affine group scheme `H` over `Spec k`, natural number `N`, and closed subgroup
homomorphism `j` into the upper triangular group specified by the statement, it
proves smoothness and connectedness of the actual scheme-theoretic kernel of
the original diagonal projection

```text
f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
           (fun i => -(i.val : ℤ)).
```

The proof introduces precisely the published hypotheses. Smoothness of `H`
supplies local finite type, so the published theorem
`triangularDiagonalSplitting`, from
`Langlands.GroupScheme.Absolute.TriangularDiagonalSplittingAssembly`, applies.
It provides group schemes and homomorphisms `d : D ⟶ L`, `q : H ⟶ D`,
`s : D ⟶ H`, where `L` is the given block Levi group, together with
closedness of `d`, `q ≫ d = f`, and `s ≫ q = id`.
Thus the section is obtained from a proved theorem without an additional
splitting hypothesis.

The closed immersion underlying `d` is a monomorphism over `Spec k`.
The block Levi scheme is a spectrum and hence affine; its structure morphism
is therefore separated. A field is noetherian. These facts discharge the
remaining hypotheses of the published theorem
`SplitKernelRetract.smooth_connected_kernel`, which is applied to the same
`f`, `d`, `q`, and `s`.

That theorem constructs the underlying scheme morphism
`h ↦ h s(q(h))⁻¹` from `H` to `kernel f`. The factorization and section
identities make it a retraction of the actual kernel inclusion. The kernel
is closed in the affine source because `L` is separated, so it is affine.
Its coordinate algebra is a retract of the smooth coordinate algebra of
`H`; formal smoothness and finite type descend to that retract, and the
noetherian base gives finite presentation. This proves smoothness.
The retraction is a continuous surjection on underlying spaces, so
connectedness follows from connectedness of `H`. The retraction need not be
a group homomorphism.

This module is a derived composition of the two published results above.
The source correspondence with Milne's diagonal kernel and Note 16.10 is
documented in the unchanged statement pair; the splitting module documents
its separate structural proof. The implementation retains every `N`,
including zero, and the full scheme-theoretic kernel, with all its scheme
structure.
