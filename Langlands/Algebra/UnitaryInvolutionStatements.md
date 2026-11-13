# Unitary involutions and the splitting of central simple algebras

Author: Worker 150.

Module: `Langlands.Algebra.UnitaryInvolutionStatements`.

This module contains three definitions and two statements about central simple
algebras with an involution of the second kind (a unitary involution). It proves
nothing. The statements are prerequisites of the outer type `A` part of Task 5973
(`LocalAnisotropicTypeAInnerStatement`). They are used through
`OuterTypeAUnitarySplitPresentationStatement`, which assumes the property
`UnitaryInvolutionSplitting K` of the base field.

## Definitions

### `Langlands.IsUnitaryInvolution`

For a commutative ring `L`, an `L`-algebra `B`, a map `σ : L → L` and a map
`τ : B → B`, the proposition `IsUnitaryInvolution σ τ` is the conjunction of:

1. `τ (x + y) = τ x + τ y` for all `x y : B`;
2. `τ (x * y) = τ y * τ x` for all `x y : B` (`τ` reverses products);
3. `τ (τ x) = x` for all `x : B`;
4. `τ (algebraMap L B l) = algebraMap L B (σ l)` for all `l : L`.

Then `τ (1) = 1`, because `τ 1 = τ (algebraMap L B 1) = algebraMap L B (σ 1)`
and `σ` will always be a ring automorphism below. When `σ` is the nontrivial
automorphism of a quadratic extension `L/K`, this is an involution of the second
kind on `B` that leaves `K` elementwise invariant, in the sense of Knus,
Merkurjev, Rost and Tignol, *The Book of Involutions*, §2.B (the definitions
before Theorem (3.1), printed p. 31). The definition makes no assumption on `σ`.

### `Langlands.UnitaryInvolutionSplitting K`

For a field `K : Type u`, `UnitaryInvolutionSplitting K` says: for every field
`L : Type u` with `Algebra K L`, `Algebra.IsQuadraticExtension K L` and
`Algebra.IsSeparable K L`, every `K`-algebra automorphism `σ : L ≃ₐ[K] L` with
`σ ≠ 1`, every `B : Type u` with `Ring B`, `Algebra L B`,
`FiniteDimensional L B`, `IsSimpleRing B` and `Algebra.IsCentral L B`, and every
`τ : B → B` with `IsUnitaryInvolution σ τ`, there are `m : ℕ` and an
`L`-algebra isomorphism `B ≃ₐ[L] Matrix (Fin m) (Fin m) L`.

In words: every central simple algebra over a separable quadratic extension of
`K` that carries a unitary involution relative to `L/K` is split. Since a
separable quadratic extension has exactly one nontrivial `K`-automorphism, the
condition `σ ≠ 1` determines `σ`.

### `Langlands.UnitaryDivisionCommutative K`

The same quantifiers as in `UnitaryInvolutionSplitting K`, but for a division
ring `D : Type u` with `Algebra L D`, `FiniteDimensional L D` and
`Algebra.IsCentral L D`, and the conclusion `Module.finrank L D = 1`.

## Statements

### `Langlands.UnitaryDivisionSplittingStatement`

For every field `K : Type u`, `UnitaryDivisionCommutative K` implies
`UnitaryInvolutionSplitting K`.

Provenance (derived). By Wedderburn's theorem a central simple `L`-algebra `B` is
`M_r(D)` for a central division `L`-algebra `D`. Knus–Merkurjev–Rost–Tignol,
Theorem (3.1) (printed p. 31, PDF p. 54), ends with: "if a central simple algebra
has an involution, then every Brauer-equivalent algebra has an involution of the
same kind". Hence `D` carries an involution of the second kind leaving `K`
elementwise invariant, i.e. a unitary involution relative to `σ`. The hypothesis
then gives `D = L`, so `B ≅ M_r(L)`. The direct argument behind the transfer of
the involution from `B` to `D` (using the idempotent `e = E₁₁` and the idempotent
`τ(e)`) is the Albert corner argument. It does not need the Brauer group.

### `Langlands.LocalUnitaryDivisionCommutativeStatement`

For every nonarchimedean local field `K : Type u` (instances `Field K`,
`ValuativeRel K`, `TopologicalSpace K`, `IsNonarchimedeanLocalField K`),
`UnitaryDivisionCommutative K` holds.

Provenance (derived). Let `D` be a central division algebra over the separable
quadratic extension `L` of the local field `K`, with a unitary involution relative
to `L/K`. By Knus–Merkurjev–Rost–Tignol, Theorem (3.1)(2) (Albert–Riehm–Scharlau,
printed p. 31, PDF p. 54), the norm (corestriction) `N_{L/K}(D)` is split. Over
local fields, Serre, *Local Fields*, Chapter XIII §3, Propositions 6 and 7
(printed p. 193, PDF p. 198), shows that `inv_K` and `inv_L` are isomorphisms onto
`ℚ/ℤ` and that `inv_L ∘ Res_{K/L} = 2 · inv_K`. Since `Res` is then surjective
and `Cor ∘ Res = 2`, it follows that `inv_K ∘ Cor_{L/K} = inv_L`. So the
corestriction is injective on Brauer groups, `[D] = 0`, and `D = L`, that is,
`Module.finrank L D = 1`. The Lean statement does not mention Brauer groups.
The intended Lean proof uses the Library's theory of local division algebras
instead, and works in every residue characteristic.

## Universe conventions

All fields and algebras quantified inside the definitions live in the universe
`u` of `K`. This matches Mathlib's Wedderburn–Artin theorem
`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`, which produces a
division ring in the universe of the given simple ring.
