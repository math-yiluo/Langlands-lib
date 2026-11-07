# Rational irreducibility under duality and coordinate changes

This internal derived unit works on the original coordinate space of a finite
matrix representation of an actual group scheme over an arbitrary field. It
identifies the rational-point action of its actual dual with the full module
dual and identifies a change of coordinates with conjugation by the same
base-field matrix. Both operations preserve rational-point irreducibility.

Let `k : Type u` be a field, `G` an actual group scheme over `Spec k`, and
`ρ : MatrixRepresentation G n`, with `n` finite and decidable. No affineness,
reducedness, algebraic closedness or characteristic assumption is made.
Here rational-point irreducibility means
`ρ.rationalRepresentation.IsIrreducible`, the simplicity of the lattice of
subrepresentations on the original space `n → k`.

`rationalDualEquiv` identifies `ρ.dual.rationalRepresentation` with the
contragredient of `ρ.rationalRepresentation`. Its linear map sends `w` to
the functional `v ↦ w ⬝ᵥ v`. The existing inverse-transpose formula for the
actual dual matrix shows that this intertwines the actions, since evaluating
the dual action is precomposition with the inverse original action.
`dual_rationalRepresentation_isIrreducible_iff` then follows from the
finite-dimensional annihilator correspondence: annihilators and
coannihilators are stable under the inverse group actions, their composites
are identities, and they reverse inclusion. Thus their invariant-subspace
lattices are order duals and are simple simultaneously.

`conjugate_rationalMatrix` maps the existing all-test matrix conjugation
formula through `Γ(Spec k, O) ≅ k`. The pullback of the conjugating base
point to the base itself is that same point. Consequently the matrix is
`C * ρ.rationalMatrix x * C⁻¹`, where `C` is the rational matrix of the
standard representation at the supplied point of `GL_n`.
`conjugateRationalEquiv` has linear map `v ↦ C *ᵥ v`; the conjugation
formula proves its intertwining identity. Simplicity transfers through the
corresponding bijective map of group-algebra modules, giving
`conjugate_rationalRepresentation_isIrreducible_iff`.

The annihilator argument generalizes the finite-dimensional complex-field
proof in `Langlands/Weil/Representation/OperationClosureProof.lean` to arbitrary
fields. The equivalence argument follows the module comparison in
`Langlands/Representation/Filtration/CentralEigenspaceSplitting.lean`.
These elementary lattice and equivalence helpers remain private.

This unit concerns the rational actions of the existing scheme
representations and supplies no group or highest-weight existence theorem,
induced-space dimension estimate or proof of `SteinbergBigCellStatement`.
The existing separate rational-to-actual irreducibility theorem remains
available when an all-affine-test conclusion is needed.
