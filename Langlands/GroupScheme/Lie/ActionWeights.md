# Weight spaces and roots of a torus acting on a Lie algebra through an action

This module defines weight spaces and roots of a commutative group scheme `T`
in the actual Lie algebra `Lie(U)(R)` of a group scheme `U`, when `T` acts on
`U` through an `AutomorphicAction H U` and a homomorphism `j : T ⟶ H`. The
action is differentiated by `AutomorphicAction.differential` from
`Langlands.GroupScheme.Lie.ActionDifferential`. The motivating case is the
action of a parabolic `P` on its unipotent subgroup `U` by `u ↦ p u p⁻¹`, with
`j` a torus in `P`. No Lie algebra homomorphism `Lie(U) → Lie(G)` is needed:
the weights are read in `Lie(U)` itself.

All declarations lie in `Langlands.GroupScheme.AutomorphicAction`. The base is
`Spec R` for an arbitrary commutative ring `R : CommRingCat.{u}`. The groups
`H` and `U` are group schemes over `Spec R` with `IsAffineHom U.X.hom`, which
the module structure on `lieKernel U A` needs. `T` is a commutative group
scheme over `Spec R`.

## Definitions

- `lieWeightSpace a j α : Submodule R (Additive (lieKernel U R))`, for
  `a : AutomorphicAction H U`, `j : T.toGrp ⟶ H` and `α : characterLattice T`.
  It is the set of `X` such that for every commutative `R`-algebra
  `A : Type u` and every `t ∈ T(A)` (`t : Lie.AffinePoints T.toGrp A`),

  `a.differential (t ≫ j) X_A = α(t) • X_A`.

  Here `X_A = lieKernelMapLinear U (Algebra.ofId R A) X` is the image of `X` in
  `Lie(U)(A)`, `t ≫ j` is the point `j(t)` of `H(A)`, and `α(t) ∈ Aˣ` is the
  published `Lie.characterValue α t`. The set is an `R`-submodule because
  `X ↦ X_A` is semilinear over `R → A` and `a.differential h` is `A`-linear.
  `mem_lieWeightSpace` unfolds membership.
- `lieRoots a j : Set (characterLattice T)` is
  `{α | α ≠ 0 ∧ lieWeightSpace a j α ≠ ⊥}` (`mem_lieRoots`). No reducedness is
  imposed: if `α` and `2α` both occur, both are roots.

The definitions copy the published `weightSpace` and `roots` of
`Langlands.GroupScheme.Torus.Weights`, replacing `adjoint U A` by the
differential of the given action. The eigenvalue condition is tested at all
points over all test algebras, not only at field-valued points.

## Comparison lemmas

- `lieWeightSpace_restrict` and `lieRoots_restrict`: for `f : K ⟶ H` and
  `j : T.toGrp ⟶ K`, the weight spaces and roots of `a.restrict f` along `j`
  are those of `a` along `j ≫ f`. The proof rewrites by the published
  `differential_restrict`. The two eigenvalue conditions then agree pointwise
  up to associativity of composition.
- `lieWeightSpace_conjugation` and `lieRoots_conjugation`: for `i : H ⟶ U`,
  the weight spaces and roots of `conjugation i` along `j` are the published
  `weightSpace (j ≫ i)` and `roots (j ≫ i)`. The proof rewrites by the
  published `differential_conjugation`, which identifies the differential of
  conjugation with `adjoint U A`.

The module states no weight decomposition, finiteness of roots or dimension
formula. Those belong to a separate statement about the restriction of the
adjoint determinant character to a split torus.

## Provenance

The construction is internal. It specializes the published Library definitions
`weightSpace` and `roots`, whose Markdown cites Milne, *Algebraic Groups*
(2017), Definition 12.16 and §21.a. Here the representation is the
differential of an arbitrary automorphic action instead of `Ad`. For a
parabolic acting on its unipotent radical, the roots defined here are the
roots of `T` occurring in `Lie(U)`. These are the roots in the product formula
for the modulus character in Renard, *Représentations des groupes réductifs
p-adiques* (version of 9 July 2026), §V.5.4, printed pp.126–127 / PDF
pp.132–133. That source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard works with a split torus over a nonarchimedean local field. This
module allows any base ring and any commutative `T`.
