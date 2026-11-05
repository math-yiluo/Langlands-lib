# Proof of complete reducibility for reductive groups in characteristic zero

Authors: Worker 1498 (group-side argument and assembly) and Worker 1429
(complete reducibility of Jordan-closed linear Lie algebras, Weyl's theorem, and
the stable-flag lemma).

## Statement proved

`Langlands.GroupScheme.reductiveCharZeroSemisimplicityStatement` proves
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement.{u}` (module
`Langlands.GroupScheme.Reductive.CharZeroSemisimplicityStatement`) for every
universe `u`. Let `k` be an algebraically closed field of characteristic zero, `G`
a group scheme over `Spec k` with `IsPseudoReductive G` (smooth, affine,
connected, with trivial unipotent radical), and `ρ : MatrixRepresentation G n`
with `n` a finite type. Then the representation of the group of `k`-points on
`n → k`, `ρ.rationalRepresentation`, is semisimple in Mathlib's sense: its lattice
of subrepresentations is complemented.

## Proof in this module

1. The fields of `IsPseudoReductive G` provide the instances `Smooth G.X.hom`,
   `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`. Smoothness implies that
   `G.X.hom` is locally of finite type. Smoothness also makes `G.X.left` reduced
   (`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`).
2. The published closed linear embedding theorem
   `Langlands.GroupScheme.affineLinearEmbeddingStatement` gives `N` and a matrix
   representation `σ : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup σ`.
3. `MatrixRepresentation.isSemisimpleRepresentation_of_isClosedSubgroup`, applied
   to the trivial unipotent radical, `σ` and `ρ`, gives the conclusion.

## Overall route

The proof is a Lie-algebra argument. The group-only routes, through Levi
decompositions or vector-group extensions, depend on statements that are not yet
proved in the Library.

- `CharZeroSemisimplicity.LieImage`: the tangent matrices of every representation
  are closed under commutators, through one bracket element `kernelBracket X Y`
  that does not depend on the representation.
- `CharZeroSemisimplicity.TangentStability`: for a smooth connected group over
  an algebraically closed field of characteristic zero, a subspace is stable under
  the rational points iff it is stable on every test iff it is stable under all
  tangent matrices. The tangent direction uses Cartier's theorem and Lie-algebra
  rigidity of smooth closed subgroups, applied to an inverse image of a block
  parabolic.
- `CharZeroSemisimplicity.JordanClosure`: tangent matrices are closed under
  Jordan semisimple parts, for any finite index type, and semisimple parts of
  block-diagonal maps are computed blockwise.
- `CharZeroSemisimplicity.FlagBasis`: bases adapted to a finite flag.
- `CharZeroSemisimplicity.NilpotentIdeal`: for a closed embedding `σ` of a group
  with trivial unipotent radical, a nilpotent family of tangent endomorphisms
  normalized by all tangent endomorphisms consists of zero tangent vectors. The
  family gives a stable flag (Worker 1429's
  `Langlands.Algebra.exists_stable_flag_of_isNilpotent`). In adapted coordinates
  it defines a closed normal unipotent subgroup whose identity component must be
  trivial.
- `CharZeroSemisimplicity.PairLieAlgebra`: the tangent Lie algebra of the pair
  `(σ, ρ)` acting on `(Fin N → k) × (n → k)` is Jordan-closed and has no nonzero
  nilpotent ideal. By Worker 1429's
  `Langlands.Algebra.complementedLattice_lieSubmodule_of_jordanClosed` (module
  `Langlands.Algebra.LinearLieSemisimplicity`, built on Weyl's theorem in
  `Langlands.Algebra.WeylCompleteReducibility`), its Lie submodules are
  complemented. A complement of `(Fin N → k) × W` projects to a rational
  complement of `W`.

Each module's Markdown explains its proofs. The route is the classical
reduction of complete reducibility for connected reductive groups in
characteristic zero to Weyl's theorem for the Lie algebra, carried out with the
Library's scheme-theoretic definitions.
