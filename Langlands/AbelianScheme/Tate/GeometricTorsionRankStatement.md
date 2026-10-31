# Rank and cardinality of actual torsion at a geometric point

`Langlands.AbelianScheme.Tate.GeometricTorsionRankStatement` is a
proposition-valued definition. It states the following theorem target without
proving it.

Let `S` be any scheme, `A : AbelianScheme S`, and `g : ℕ`. Assume
`A.HasRelativeDimension g`, the existing predicate
`SmoothOfRelativeDimension g A.X.hom`. Let `n` be positive and suppose its
image in `Γ(S, ⊤)` is a unit. For every algebraically closed field `Ω` in the
scheme's universe and every morphism `s : Spec Ω ⟶ S`, the conclusions are:

- There exists a `ZMod n`-linear equivalence from
  `Fin (2 * g) → ZMod n` to
  `GroupScheme.Tate.Level A.toGrp (Over.mk s) n`.
- The natural-number cardinality of this actual torsion group is
  `n ^ (2 * g)`.

The first assertion uses `Nonempty` to express existence without choosing a
basis. It implies finiteness; the second assertion records its numerical
consequence explicitly. Both `n = 1` and `g = 0` are included.

## Actual torsion and hypotheses

The target is the published `Level` from [`Integral`](Integral.md), namely
the additive group of actual sections over `Over.mk s` killed by
multiplication by `n`. The additive equivalence `kernelLevelEquiv` in that
module identifies it with points of the scheme-theoretic multiplication
kernel. Thus the statement concerns the geometric fibre of actual `A[n]`,
without taking an unrelated group or a supplied rank as input.

The scalar action is the existing `GroupScheme.Tate.levelZModModule` from
[`PrimeAdic`](PrimeAdic.md). Despite that module's name, this instance is
defined for every natural-number level `n`: the proved relation
`n • x = 0` induces the residue-class action. No basis, comparison
equivalence, or compatible family of bases is assumed.

The dimension `g` is attached to the actual smooth structure morphism. The
statement does not require that every abelian scheme have a single constant
relative dimension. It requires neither connectedness, quasi-separatedness,
nor local noetherianity of `S`. Positivity excludes level zero, and the base
unit condition ensures that `n` is prime to the characteristic after
specializing to the point field.

## Source correspondence and relative specialization

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, Chapter V (5.9) and (5.11), printed
pp.74–75 (PDF pp.78–79). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These original pages and the following printed p.76 were read directly.

The source works over a field. Proposition (5.9) gives degree `n^(2g)` for
multiplication by a nonzero integer on a `g`-dimensional abelian variety,
and separability when the characteristic does not divide `n`. Corollary
(5.11) identifies its geometric torsion group with `(ℤ/nℤ)^(2g)` in that
case. Its proof uses finite étaleness and order `n^(2g)`, the orders of
torsion subgroups for every divisor of `n`, and the structure theorem for
finite abelian groups.

The Lean target is a derived relative geometric-point formulation of this
field result. Proving it requires passing to the actual abelian scheme
pulled back along `s`, relating its dimension to the stated smooth relative
dimension, transferring the base unit condition to `Ω`, and identifying its
torsion points with the displayed `Level`. The published
`AbelianScheme.baseChange` and `hasRelativeDimension_baseChange` provide the
pullback and preservation of the relative-dimension predicate. The
`GroupScheme.Tate.fibreLevelEquiv` from `Integral` identifies sections of the
pulled-back kernel with `Level` as types. Its existence alone does not give
the additive and residue-linear identification needed for this argument.
These geometric and algebraic comparisons remain proof obligations.

An additive group isomorphism between groups killed by `n` respects the
residue actions, because these actions come from integer multiplication.
This explains the `ZMod n`-linear formulation of the source's group
isomorphism. It does not assume that the necessary actual-fibre
isomorphism has already been constructed.

## Status and scope

This module supplies a statement, not its proof or a chosen trivialization.
The numerical conclusion is the cardinality of a geometric fibre. A theorem
about the rank of a finite locally free scheme over `S` is a separate
statement. Finite étaleness of the actual torsion scheme is covered by
[`TorsionFiniteEtaleStatement`](../TorsionFiniteEtaleStatement.md) and its
separate proof; finite étaleness alone does not establish this rank.

The target asserts no compatibility of bases at different levels, no
relative scheme trivialization, no monodromy equivariance, and no assertion
at a characteristic-divisible level. It also does not prove inverse-limit
freeness or rational dimension. Those are the separate targets of
[`GeometricPrimeAdicRankStatement`](GeometricPrimeAdicRankStatement.md);
this finite-level result can serve as one prerequisite of their proof.
