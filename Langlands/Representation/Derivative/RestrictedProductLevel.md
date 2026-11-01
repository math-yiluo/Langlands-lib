# Homogeneity of the restriction of a binary product

Module `Langlands.Representation.Derivative.RestrictedProductLevel`, namespace
`Langlands.Derivative.RestrictedProductLevel`.

Let `D` be a representation of `GL_(m+1)` and `P` one of `GL_(n+1)`. The
restriction of `D × P` to the mirabolic subgroup `P_(m+n+2)` has a short
exact sequence (BZ77 Proposition 4.13(a))

`0 → σ = (D|P) × P → (D × P)|P → τ = D × (P|P) → 0`,

with `σ` a right mixed product and `τ` a left mixed product. Suppose every
nonzero derivative of `D|P` has order `s + 1` and `Y = (D|P)^(s+1) × P|P` is
homogeneous. The main theorem, `isHomogeneous_restrictedProduct`, says that
`(D × P)|P` is homogeneous provided no nonzero representation injects both
into `(D × P)|P` and into `τ`. This is the induction step of Zelevinsky's
proof of Theorem 6.2 (`zelevinsky-1980-induced-ii`, proof in §6.3, printed
pp.188–189, following BZ77 §4.15). The excluded situation is Case 2 of that
proof. Excluding it is a separate argument: here it is the **explicit
hypothesis** `hC2`.

## Hypotheses

All lower inputs are published Library propositions taken as **explicit
hypotheses**. None is proved here.

| Hypothesis | Published proposition | Source |
| --- | --- | --- |
| `hE` | `Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T` | exactness of `Ψ⁻`, `Φ⁻` (BZ77 3.2) |
| `hD` | `RightMixedProductPhiMinusDetection.{uF, uV} F T` | BZ77 4.13(d) |
| `hS` | `MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T` | BZ77 4.13(c) |
| `hB` | `MirabolicProductMinus.RightPhiBoundary.{uF, uV} F T` | BZ77 4.13(c), `P_1` boundary |
| `hR` | `MirabolicProductRestrictionStatement.{uF, uV} F T` | BZ77 4.13(a) |
| `hLD` | `LeftMixedProductDerivative.{uF, uV} F T` | BZ77 4.14(a) |

## Provenance

This is internal derived material. It formalizes the case split of BZ77 §4.15
as adapted by Zelevinsky §6.3 (`bernstein-zelevinsky-1977-induced-i`;
`zelevinsky-1980-induced-ii`, printed pp.188–189). Let `ω` be a nonzero
submodule of `(D × P)|P`. Either `ω ∩ σ ≠ 0` (Case 1), or `ω` embeds into `τ`
(Case 2). The level bounds through 4.14(a) are the routine part of that
argument.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`, `T : F.TopologicalData` and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology` are fixed, with
`T.topology` installed. Factor carriers are in `Type uV`; products have
carriers in `Type (max uF uV)`. In namespace
`MirabolicProductRestriction`, `restrictedProduct T m n`,
`restrictionSubobject T m n` and `restrictionQuotient T m n` are the published
functors giving `(D × P)|P`, `σ` and `τ` (all on `mirabolic (m+n+1)`).
`generalLinearRestriction T m` restricts from `GL_(m+1)` to `P_(m+1)`.

## Declarations

### Comparisons (section `Comparison`)

- `level_le_of_imp_of_rank A B h`: for `A` on `P_(N+1)` (carrier in `uV`) and
  `B` on `P_(M+1)` (carrier in `uW`), possibly of different ranks and
  universes: if every nonzero derivative order of `A` is one of `B`, then
  `level A ≤ level B`.
The rank-transport fact `RestrictionBridge.nontrivial_generalLinearRankCast_iff`
is reused from [RestrictionBridge](RestrictionBridge.md): rank transport of `GL`
representations preserves nontriviality.

### Levels of left mixed products (section `LeftLevel`, hypothesis `hLD`)

Here `ρ` is on `GL_k` and `τ` on `P_(r+1)`; `ρ × τ` is their left mixed
product on `P_(k+r+1)`.

- `hasNonzeroDerivative_of_leftMixed`: if `ρ × τ` has a nonzero derivative of
  order `i`, so does `τ`. For `i ≤ r + 1`, 4.14(a) identifies the derivative
  with `ρ × τ^(i)`, which vanishes if `τ^(i)` does
  (`ProductVanishing.subsingleton_binary`). For `i > r + 1` the derivative
  vanishes by the second part of 4.14(a).
- `hasNonzeroDerivative_leftMixed`: if `ρ ≠ 0` and `τ` has a nonzero derivative
  of order `i`, so does `ρ × τ` (`ProductVanishing.nontrivial_binary` and
  4.14(a)).
- `level_leftMixed_le`: `level (ρ × τ) ≤ level τ`.
- `le_level_leftMixed`: if `ρ ≠ 0`, `level τ ≤ level (ρ × τ)`.

### The restricted binary product (section `Main`, all six hypotheses)

`isHomogeneous_restrictedProduct m n n' s hm D P hDj hY hC2`: let
`hm : m = n' + s`, `D` on `GL_(m+1)` and `P` on `GL_(n+1)`. Assume:

- `hDj`: every nonzero derivative order of `D|P` (on `P_(m+1)`) is `s + 1`;
- `hY`: `Y = (T.leftMixedProductFunctor n' n).obj
  ((mirabolicDerivative T ψ n' s).obj (cast (D|P)), P|P)` is homogeneous, where
  the first entry is the order-`(s+1)` derivative of `D|P`, a representation of
  `GL_(n')`;
- `hC2`: there is no nontrivial `W` (carrier in `max uF uV`, on
  `mirabolic (m+n+1)`) with injective intertwiners both into
  `(restrictedProduct T m n).obj (D, P)` and into
  `(restrictionQuotient T m n).obj (D, P)`.

Then `IsHomogeneous T ψ ((restrictedProduct T m n).obj (D, P))`.

Proof. Let `i`, `q` be the short exact sequence of `hR`, and put
`c = level Y + (s + 1)`. By `RightMixedLevel.level_of_injective_rightMixed`
(with `hE hD hS hB`, `hDj`, `hY`), every nontrivial representation injecting
into `σ` has level `c`. By `LevelCalculus.isHomogeneous_of_forall_injective`
it suffices to show `level W = c` for every nontrivial `W` with an injection
`f : W ⟶ (D × P)|P`. Let `W₁ = f⁻¹(range i)` (`LevelCalculus.comap`).

- If `W₁ = 0`, then `f ≫ q` is injective, because `ker q = range i`.
  This contradicts `hC2`.
- Otherwise `W₁` is nontrivial and injects into `σ` (`comapMap` and
  `isoRange`), so `level W₁ = c`; likewise `level σ = c`. Exactness (`hE`)
  gives `c = level W₁ ≤ level W ≤ level ((D × P)|P)`.
  `LevelCalculus.level_le_max_of_isShortExact` gives
  `level ((D × P)|P) ≤ max (level σ) (level τ)`. Finally
  `level τ ≤ level (P|P) ≤ level Y ≤ c`. The first inequality is
  `level_leftMixed_le`. The second is `le_level_leftMixed`, since the first
  factor `(D|P)^(s+1)` of `Y` is nonzero. Indeed `D|P ≠ 0`, because `σ ≠ 0`
  (`ProductVanishing.subsingleton_rightMixed`), so `D|P` has level `s + 1` by
  detection.
  Hence `level W = c`.
