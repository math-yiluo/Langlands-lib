# Inner forms of `Sp_{2n}` are symplectic groups of antihermitian division forms: statement

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`). The module
contains one `Prop`-valued definition and no proof.

## Statement

`Langlands.GroupScheme.SymplecticInnerFormAntihermitianStatement.{u}` quantifies over

- a field `K : Type u`;
- a group scheme `G` over `Spec K`, with no further hypothesis;
- a natural number `n` with `2 ≤ n`;
- an actual quasi-split inner-form presentation `q : QuasiSplitInnerForm G` (module
  `Rational/QuasiSplitInnerForm`).

Assume that the model group `q.model` is isomorphic, as a group scheme over `Spec K`, to
`Symplectic.groupScheme K n`, the standard symplectic group scheme `Sp_{2n}` (the isometry
group of `Matrix.J (Fin n) K`, module `Symplectic/Basic`). The statement then asserts that
there are

- natural numbers `degree` and `m`, with `NeZero m`, `0 < degree` and `m * degree = 2 * n`;
- a division ring `D : Type u` which is a central, finite-dimensional `K`-algebra with
  `Module.finrank K D = degree ^ 2`;
- an involution of the first kind `σ : Quaternionic.FirstKindInvolution K D` whose space of
  symmetric elements `σ.symmetricSubspace = {x | σ x = x}` has `K`-dimension
  `degree * (degree + 1) / 2`;
- a Gram matrix `H : Matrix (Fin m) (Fin m) D` with `σ.IsAntihermitian H` and `IsUnit H`,

such that `G` is isomorphic, as a group scheme over `Spec K`, to `σ.symplecticGroup H`.

Here `σ.IsAntihermitian H` (module `Quaternionic/Forms`) means `ᵗH^σ = -H` and every diagonal
entry `H i i` lies in `{a - σ a}`; the second condition matters in characteristic two. The
group `σ.symplecticGroup H` (module `Quaternionic/GroupSchemes`) is the kernel of the reduced
norm on the unitary group scheme of `H`, whose points with values in a commutative
`K`-algebra `R` are the units `u` of `R ⊗[K] M_m(D)` with `u H ᵗu^σ = H`. The conclusion
consists of exactly the algebra, involution, form and isomorphism data of the published
`TypeCDivisionFormStatement`, without its split-rank and distinguished-vertex clauses.

When the characteristic of `K` is not two, the dimension condition on `σ.symmetricSubspace`
says that `σ` is of orthogonal type (Knus–Merkurjev–Rost–Tignol, Proposition (2.6)(1)). In
characteristic two every involution of the first kind satisfies it (Proposition (2.6)(2)); there
the trace-valued condition on `H` is what makes the adjoint involution symplectic (Theorem
(4.2)). For `degree = 1`, `D = K` and `σ` is the identity.

## Intended proof (not part of the statement)

The adjoint quotient of `Sp_{2n}` is `PSp_{2n} = Aut(M_{2n}, ad_J)`, the automorphism group
of the matrix algebra with the symplectic involution adjoint to the standard alternating
form. Twisting `(M_{2n}(L), ad_J)` by the cocycle of `q` and Galois descent give a central
simple `K`-algebra `A` of degree `2n` with a symplectic involution `τ`, and `G ≅ Sp(A, τ)`.
Write `A ≅ M_m(D)` with `D` a central division algebra of degree `degree`, so
`m * degree = 2n`. `D` carries an involution of the first kind `σ` of orthogonal type, whose
symmetric space has the required dimension by Proposition (2.6), and by
Knus–Merkurjev–Rost–Tignol Theorem (4.2) `τ` is the adjoint involution of a nonsingular
skew-hermitian form `h` on `D^m` with respect to `σ`, which in characteristic two is
alternating; its Gram matrix is the required `H`. On `Sp(A, τ)` the reduced norm is trivial,
which identifies `Sp(A, τ)` with `σ.symplecticGroup H`.

## Role

This is one of four prerequisites in the planned proof of
`TypeCDivisionFormStatement` (Task 5986). It consumes the conclusion of
`TypeCQuasiSplitInnerFormStatement`; the other two prerequisites are
`AntihermitianSymplecticSplitRankStatement` and `TypeCDistinguishedVerticesStatement`.

## Source and provenance

Provenance: derived.

1. M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
   Colloquium Publications 44, 1998, source `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
   SHA-256 `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`:
   - §26, Theorem (26.14), printed p.369 (PDF p.392): over an arbitrary field, the functor
     `(A, σ) ↦ Sp(A, σ)` is an equivalence from central simple algebras of degree `2n` with
     symplectic involution onto simply connected simple groups of type `C_n`; its proof
     (printed pp.369–370, PDF pp.392–393) obtains every such group by twisting the split
     object by a cocycle of `PGSp = Aut(A, σ)`;
   - §4, Theorem (4.2), printed p.43 (PDF p.66): for `A = End_D(M)` and an involution `θ` of
     the first kind on `D`, `h ↦ σ_h` is a bijection from nonsingular hermitian and
     skew-hermitian forms up to scalars onto involutions of the first kind; if `char F ≠ 2`
     the types of `σ_h` and `θ` are opposite when `h` is skew-hermitian, and if `char F = 2`,
     `σ_h` is symplectic exactly when `h` is alternating;
   - §2, Proposition (2.6), printed pp.16–17 (PDF pp.39–40): for an involution of the first
     kind on a central simple algebra of degree `d`, if `char F ≠ 2` the symmetric space has
     dimension `d(d + 1)/2` for orthogonal and `d(d - 1)/2` for symplectic type, and if
     `char F = 2` it has dimension `d(d + 1)/2` in both cases.
2. J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic Groups and
   Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, 1966, source
   `tits-1966-classification-algebraic-semisimple`, SHA-256
   `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`, Table II, type `C_n`,
   printed p.56 (PDF p.61): the groups are `SU_{2n/d}(D, h)` with `D` a division algebra of
   degree `d` and `h` a nondegenerate antihermitian form relative to an involution of the
   first kind with `dim D^σ = d(d + 1)/2`; for `d = 1` the group is `Sp_{2n}(k)`.

The Lean statement is derived from these sources as follows. "Inner form of `Sp_{2n}`" is the
published `QuasiSplitInnerForm` presentation with model isomorphic to
`Symplectic.groupScheme K n`. Tits's `SU_{2n/d}(D, h)` is the published
`σ.symplecticGroup H` with `m = 2n/d`, and the antihermitian condition is the published
trace-valued `σ.IsAntihermitian`, which is the alternating condition of Knus–Merkurjev–Rost–
Tignol in characteristic two. Tits describes groups of rational points; the statement asks for
an isomorphism of group schemes. Knus–Merkurjev–Rost–Tignol state the classification over an
arbitrary field, in every characteristic.
