# The p-adic norm of an actual Tate determinant and the point kernel

`Langlands.AbelianScheme.GeometricTateDeterminantKernelStatement.{u}` is an
unproved proposition in arbitrary universe `u`. It concerns every actual
abelian scheme `A` over `Spec k`, for an algebraically closed field `k : Type u`
of characteristic zero, every prime `p`, and every actual integral
endomorphism `f : End A`. It equates the standard real-valued p-adic norm of
the determinant of `f` on the actual rational Tate module with the norm of
the natural cardinality of the actual kernel on `k`-valued points, cast into
`ℚ_[p]`.

The source is J. S. Milne, *Abelian Varieties*, January 2, 2022 author revision,
§12, proof of Proposition 12.9, p.23 (also one-based PDF page 23), source ID
`milne-abelian-varieties-1986-author-2022`. The complete registered errata
snapshot was read; its corrections are incorporated in this revision.
The source equates the p-adic norm of the kernel cardinality with the
reciprocal cardinality of its p-primary part, then with the reciprocal
cardinality of the cokernel on the integral Tate module, then with the norm
of its determinant. This statement isolates the equality between the first
and last quantities. Restricting to an algebraically closed
characteristic-zero base is deliberate; every prime is then different from
the characteristic.

`groupHom f` is the actual group-scheme homomorphism underlying `f`.
`GroupScheme.pointsHom` applies it to sections over
`Over.mk (𝟙 (Spec (CommRingCat.of k)))`; these are the actual `k`-valued
points. Its kernel is a subgroup of that group of sections. No replacement
kernel or abstract finite-group model is supplied as data.
`Tate.PrimeAdic.rationalMap` is the scalar extension to `ℚ_[p]` of the map
on the actual inverse limit of prime-power torsion sections at that same
point. `LinearMap.det` takes its determinant over `ℚ_[p]`. Finite
dimensionality of this actual module is a consequence of the published
geometric Tate-rank theorem; it is not a hypothesis that could restrict the
scheme or the endomorphism in this statement.

For an isogeny, the actual point kernel is finite and the norm of its
cardinality is the reciprocal of the order of its p-primary subgroup.
The quantifier over `f` also includes nonisogenies. Lean's `Nat.card` is zero
for an infinite type, so in the nonisogeny case the assertion includes the
vanishing of the determinant. Establishing that the point kernel is
infinite in that case, and proving the corresponding vanishing, are
obligations of a proof of this statement. No isogeny assumption or supplied
finite-kernel premise is added.

This file does not define geometric degree, identify native finite-flat
rank with point-kernel cardinality, or prove the determinant equality.
It is a focused bridge needed in the proof of geometric trace comparison.
