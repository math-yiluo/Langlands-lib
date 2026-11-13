# Symplectic splitting charts and norm-one involution isometries

This module supplies internal interfaces for constructing the algebra with
involution associated with an inner form of the standard symplectic group.
All fields, coefficient rings and characteristics, including characteristic two,
are retained.

For an involution of the first kind `τ` on a `K`-algebra `A`,
`HasStandardSymplecticSplitting τ n` requires an actual finite Galois extension
`L/K` and an `L`-algebra isomorphism
`e : L ⊗[K] A ≃ₐ[L] M_(Fin n ⊕ Fin n)(L)` satisfying

`e (τ_L(x)) J = J (e x)ᵀ`.

Here `J = Matrix.J (Fin n) L` is the standard nondegenerate alternating matrix.
Since `J` is invertible, this identifies the extended involution with the adjoint
involution of `J`. In characteristic two, the alternating matrix condition
retains the symplectic type; a dimension condition on symmetric elements alone
would not do so. This predicate explicitly asks for the splitting chart. The
module does not prove existence of such a chart for an arbitrary involution.

For finite-dimensional `A`, `isometryGroup τ` specializes the published
`Quaternionic.IsometryCut.groupScheme` to the zero subspace and `Q = 1`. Its
points over any relative test scheme `T`, with coefficient algebra `R = Γ(T)`,
are precisely the units `u` of `R ⊗[K] A` satisfying `u τ_R(u) = 1`.
`isometryι` is the published closed inclusion of that cut into the unit group.
`mem_range_isometryι_iff` states this equation on every test scheme.

When `A` is also central simple, `normOneGroup τ` is the kernel of the actual
reduced norm restricted to `isometryGroup τ`. The maps `normOneGroupι` and
`normOneAmbientι` are its inclusions into the isometry and algebra-unit groups.
The latter is a monomorphism and represents its subgroup-functor range.
`mem_range_normOneGroupι_iff` is the kernel membership criterion, and
`mem_range_normOneAmbientι_iff` expresses ambient membership as the conjunction
of the isometry equation and reduced norm one. Their proofs use the published
kernel criterion and composition of the two inclusions.

These are derived constructions, specialized from the published isometry cuts,
algebra-unit groups and unconditional reduced norm. The finite Galois chart
packages the split symplectic involution used in the descent argument of
Knus–Merkurjev–Rost–Tignol, *The Book of Involutions* (1998), Theorem (26.14),
printed pp.369–370. The use of an alternating splitting matrix agrees with their
Definition (2.5) and Proposition (2.6), printed pp.16–17. The norm-one cut follows
the convention of the Library's `Quaternionic.FirstKindInvolution.symplecticGroup`.
No classification theorem is proved or assumed by these definitions.
