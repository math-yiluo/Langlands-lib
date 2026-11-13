# Symplectic inner forms as algebras with involution: descent target

`Langlands.GroupScheme.SymplecticInnerFormInvolutionStatement.{u}` isolates the
algebra-with-involution descent step needed for the antihermitian division-form
description of inner forms of `Sp_{2n}`.

For any field `K : Type u`, group scheme `G` over `Spec K`, integer `n ≥ 2`,
actual quasi-split inner-form presentation `q : QuasiSplitInnerForm G`, and
isomorphism between `q.model` and the standard `Symplectic.groupScheme K n`,
the proposition requires:

- a finite-dimensional central simple `K`-algebra `A : Type u` with reduced
  degree `2 * n`;
- an involution of the first kind `τ` on `A` and an actual finite Galois
  extension `L/K` with an algebra chart identifying `τ_L` with the adjoint
  involution of the standard alternating matrix `J`;
- an isomorphism of group schemes over `Spec K` between `G` and the
  reduced-norm-one involution-isometry group `SymplecticInnerForm.normOneGroup τ`.

The chart is the predicate `HasStandardSymplecticSplitting τ n` defined in
`SymplecticInnerForm.InvolutionModel`. Its equation is
`e (τ_L(x)) J = J (e x)ᵀ`. Requiring this equation retains symplectic type in
characteristic two. The group is the kernel of reduced norm on the represented
subgroup of algebra units satisfying `u τ(u) = 1`. The conclusion concerns actual
group schemes and hence all relative tests.

This is a derived prerequisite statement specializing the descent step of
Knus–Merkurjev–Rost–Tignol, *The Book of Involutions* (1998), Theorem (26.14),
printed pp.369–370. Their category of degree `2n` central simple algebras with
symplectic involution is equivalent to the category of simply connected groups
of type `C_n`, for `n > 1`. The present statement starts with an explicit inner
twisting of the split symplectic model, retaining the finite Galois extension and
the discrepancy on all relative tests in `QuasiSplitInnerForm`.

The intended construction twists the split matrix algebra and its alternating
adjoint involution by that discrepancy, descends both operations, and compares
the represented isometry groups using their common descent datum. Finiteness of
the splitting extension is part of the finite Galois input retained in `q`.
The reduced-norm-one convention matches the division-form symplectic group used
by the consumer. Expressing the descended algebra as a matrix algebra over a
division algebra and constructing its antihermitian form are separate algebraic
steps. This module defines the proposition and supplies no proof of the descent
or of the final division-form classification.
