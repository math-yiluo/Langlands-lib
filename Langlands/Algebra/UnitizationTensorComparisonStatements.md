# Renard I.2.1: the unitized tensor comparison and the algebra structure on the unitization

Module `Langlands.Algebra.UnitizationTensorComparisonStatements`.
Namespace `Langlands.Algebra.UnitizationTensorComparison`.
Entry proposition `Statements`.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.2.1 "Structure d'espace
vectoriel sur les modules non dégénérés", printed p.14 / PDF20. Registered
source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The page reads (French original):

> Si `A` est une ℂ-algèbre sans unité, il n'y a pas de structure de
> ℂ-espace vectoriel canonique sur `Hom_A(X, Y)` ou sur `X ⊗_A Y`, même
> lorsque `X` et `Y` sont des espaces vectoriels. Ceci est extrêmement
> gênant, et l'on y remédie en introduisant l'algèbre unitaire
> `Ã = A ⊕ ℂ·1_A`, où l'on décide que `1_A` est l'unité de `Ã` (ceci
> détermine une unique structure d'algèbre sur `Ã`). Si `X` et `Y` sont deux
> `A`-modules et aussi des ℂ-espaces vectoriels, ils deviennent naturellement
> des `Ã`-modules unitaires et l'on a
> `Hom_Ã(X, Y) = Hom_A(X, Y) ∩ Hom_ℂ(X, Y)`,
> `X ⊗_Ã Y = X ⊗_A Y / Vect({λx ⊗ y − x ⊗ λy, x ∈ X, y ∈ Y, λ ∈ ℂ})`,
> où `Vect(P)` désigne le sous-espace engendré par une partie `P` d'un espace
> vectoriel. Si `A` est une algèbre à idempotents, d'après ce qui précède, si
> `X` et `Y` sont deux `A`-modules non dégénérés,
> (I.2.1.2) `Hom_Ã(X, Y) = Hom_A(X, Y)`, `X ⊗_Ã Y = X ⊗_A Y`
> pour les structures canoniques de ℂ-espace vectoriel sur `X` et `Y`. Ceci
> est vrai en particulier si `A`, ainsi que les modules `X` et `Y`, sont
> unitaires.

The published note `notes/renard/unitization-tensor-progress.md` (Worker 709)
maps every assertion of I.2.1 to the Library. It records three assertions of
this passage with no published statement. This unit states those three, plus
the unital special case introduced by "en particulier". The note's labels are:

- (f) "ceci détermine une unique structure d'algèbre sur `Ã`".
- (i) `X ⊗_Ã Y = X ⊗_A Y / Vect({λx ⊗ y − x ⊗ λy})`.
- (j) (I.2.1.2), tensor half: `X ⊗_Ã Y = X ⊗_A Y` for an algebra with
  idempotents and nondegenerate `X`, `Y` with their canonical scalars.
- (k) "Ceci est vrai en particulier si `A`, ainsi que les modules `X` et `Y`,
  sont unitaires", tensor half.

The Hom halves of (j) and (k) are already published as
`NondegenerateModuleHomScalars.unitizedHomEquiv`. This unit states only the
tensor halves.

"Ils deviennent naturellement des `Ã`-modules unitaires" uses the
compatibility (I.2.1.1) of the scalars with the action of `A`, stated on the
same page. The statements below therefore assume it, as scalar-tower and
commuting-action hypotheses.

The source works with complex algebras. All four statements take an arbitrary
commutative ring `k` in place of `ℂ`, as the published constructions they use
already do. `k = ℂ` is the source case. Four parts of the formulation are
internal choices, explained below: the integer span for `Vect`, the
bilinear-multiplication form of (f), the explicit existence clauses of (f), and
the grouping of the four statements.

## The objects

All declarations come from the Library, with no new construction:

- `CompatibleUnitizationTensor.comparison k A X Y` is `q : TA →+ TU`, the lift of
  the pure map from the published balanced tensor `TA = X ⊗_A Y` to the
  published balanced tensor `TU = X ⊗_Ã Y`. Here `Ã` is Mathlib's
  `Unitization k A`, acting through `CompatibleUnitization.module`.
- `CompatibleUnitizationTensor.scalarRelations k A X Y` is `H`, the integer span
  in `TA` of the differences `tmul (c • x) y − tmul x (c • y)`.
- `CompatibleUnitizationTensor.descendedComparison k A X Y` is
  `qbar : TA ⧸ H →+ TU`, the descent of `q`.
- `NondegenerateTensorScalars.rightModule k hA hX` and `leftModule k hA hY` are
  the published canonical scalars `c • m = (c • e) • m` on the right factor
  (over `Aᵐᵒᵖ`) and on the left factor. `NondegenerateScalars.isScalarTower` and
  `smulCommClass` are the published proofs of (I.2.1.1) for them.
- `NondegenerateScalars.unitalModule k h` is the published unital canonical
  scalar module `c • m = (c • 1) • m`.
- `LinearMap.mul k (Unitization k A)` is Mathlib's multiplication of
  `Unitization k A`, as a `k`-bilinear map.

A right module is a `NonUnitalModule Aᵐᵒᵖ X`, as in the published modules.

## Proposition definitions

Every declaration in this file is a `Prop`-valued definition. Each one is closed
and quantifies over its universe-polymorphic data, with independent universes
`uK` (scalars), `uA` (algebra), `uX` and `uY` (the two factors).

### `ScalarQuotientComparisonStatement` (assertion (i))

Take a commutative ring `k` and a nonunital `k`-algebra `A`
(`[Module k A] [IsScalarTower k A A] [SMulCommClass k A A]`). Take a right module
`X` and a left module `Y`, each with a `k`-module structure compatible with the
action (scalar tower and commuting actions). Then:

1. `LinearMap.ker q.toIntLinearMap = H`, and
2. `qbar` is bijective.

This is the source's `X ⊗_Ã Y = X ⊗_A Y / Vect(...)`. The published `H` takes the
integer span because `X ⊗_A Y` carries no canonical `k`-module structure here,
as the source itself observes ("il n'y a pas de structure de ℂ-espace
vectoriel canonique sur ... `X ⊗_A Y`"). The published module's "integer-span
convention" documents this choice. The relations `λx ⊗ y − x ⊗ λy` are exactly
the generators of `H`. Whenever scalars act on `X ⊗_A Y` through the left
factor, the integer span is already stable under them, since
`c·(λx ⊗ y − x ⊗ λy) = λ(cx) ⊗ y − (cx) ⊗ λy`; so it is then the source's
`Vect`. No nondegeneracy or idempotented hypothesis is assumed;
the source states (i) at this generality, before (j).

### `NondegenerateUnitizedTensorStatement` (assertion (j), tensor half)

Take `k`, `A` as above, an idempotented `A` (`hA : IsIdempotented A`), a
nondegenerate right module `X` (`hX : IsNondegenerate Aᵐᵒᵖ X`) and a
nondegenerate left module `Y` (`hY : IsNondegenerate A Y`), with no scalar
structure supplied on either carrier. Install the published canonical scalars
and their published compatibility proofs on both factors. Then `q` is bijective,
that is, `X ⊗_A Y = X ⊗_Ã Y` via the canonical comparison.

### `UnitalUnitizedTensorStatement` (assertion (k), tensor half)

Take a unital `k`-algebra `R` (`[Ring R] [Algebra k R]`), a unital right module
`X` (`hX : IsUnitalModule Rᵐᵒᵖ X`) and a unital left module `Y`
(`hY : IsUnitalModule R Y`). Install the published unital canonical scalars
`NondegenerateScalars.unitalModule`. Their compatibility proofs are the
published ones at `IsIdempotented.of_ring` and
`isNondegenerate_iff_isUnitalModule.mpr`. Then `q : X ⊗_R Y →+ X ⊗_R̃ Y` is
bijective. Here `R̃` is still `Unitization k R`, the source's `Ã` for unital
`A`. Mathlib's `Algebra k R` supplies the `Module k R`, scalar-tower and
commuting instances that the comparison needs.

### `UnitizationAlgebraUniqueStatement` (assertion (f))

For `k`, `A` as above, the statement is a conjunction of two parts.

1. Existence. The multiplication of Mathlib's `Unitization k A` (the module
   `k × A`, with `inl` and the coercion `inr`) is associative, has `1 = inl 1`
   as a two-sided unit, and extends the multiplication of `A`:
   `(a : Ã) * (b : Ã) = ((a * b : A) : Ã)`.
2. Uniqueness. Every `k`-bilinear map
   `μ : Ã →ₗ[k] Ã →ₗ[k] Ã` with `μ 1 u = u`, `μ u 1 = u` and
   `μ a b = a * b` on `A` equals `LinearMap.mul k (Unitization k A)`.

This is "ceci détermine une unique structure d'algèbre sur `Ã`". An algebra
structure on the vector space `A ⊕ k·1` is a bilinear associative
multiplication, and "`1_A` est décrété être l'unité" together with the
inclusion of `A` as a subalgebra gives the three conditions. The uniqueness
clause asks for neither associativity nor any other property of `μ`, so it is
at least as strong as uniqueness among algebra structures. The existence clause
makes explicit that the unique structure is Mathlib's.

### `Statements`

The conjunction of the four propositions above, in the order (i), (j), (k), (f),
with universe parameters `uK uA uX uY`.

## Scope and dependencies

This file states these four assertions and proves none of them. Proofs belong
to a separate `lean.proof@1` task targeting `Statements` (or its components).
A complete compiled proof exists privately in Worker 1222's drafts. It is not
evidence for this unit.

The file imports `Langlands.Algebra.CompatibleUnitizationTensor`,
`Langlands.Algebra.NondegenerateTensorScalars` and pinned Mathlib
`Mathlib.Algebra.Algebra.Bilinear` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). It makes the published opposite
adapters `NondegenerateTensorScalars.opIsScalarTower` and `opSMulCommClass`
local instances, as `NondegenerateTensorScalars` itself does, so that the
canonical scalars on the right factor elaborate.

The remark that a nonunital `A` gives no canonical vector-space structure on
`Hom_A(X, Y)` or `X ⊗_A Y` (the note's (e)) remains an informal remark with no
statement. The
rest of I.2 retains its separate obligations.
