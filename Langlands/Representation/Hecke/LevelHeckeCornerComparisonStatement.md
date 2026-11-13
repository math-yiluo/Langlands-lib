# The measure-free level Hecke algebra and the Haar-measure `H(G, K)`: statement

Module `Langlands.Representation.Hecke.LevelHeckeCornerComparisonStatement`. Namespace
`Langlands.Hecke`. Universe parameters `u` (the group) and `v` (representation spaces).
The module contains one **statement**, the `Prop`-valued definition
`LevelHeckeCornerComparisonStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. It is a **derived comparison**, not a numbered assertion
of the source. The Library has two models of the Hecke algebra `H(G, K)` of a compact open
subgroup:

- Renard's model (III.1.5, II.3.12): the corner `e_K H(G) e_K` of bi-`K`-invariant test
  functions with convolution for a Haar measure, `HeckeAlgebra.Corner μ K hK`
  ([Corner](Corner.md));
- the measure-free model `LevelHeckeAlgebra ℂ K` of left `K`-invariant finitely supported
  functions on `G/K` with coset convolution, acting on `K`-fixed vectors by
  `a • v = Σ_{xK} a(xK) ρ(x) v` (`Langlands/Shimura/LevelHeckeAlgebra.lean`).

The published VI.9.4 statement `Jacquet.StandardFixedVectorHeckeEquivalenceStatement` is
formulated with `LevelHeckeAlgebra ℂ K`. The Chapter VI item ledger lists "the comparison of
`LevelHeckeAlgebra ℂ K` with the Haar-measure `H(G, K)`" as part of a gap. This unit states that
comparison.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read:

- III.1.5, printed p.60 / PDF p.66: "Rappelons que `e_K ∗ H(G) ∗ e_K = H(G, K)`", and
  Proposition (i): `j_K(V) = e_K · V` is `V^K`. So `H(G, K)` acts on `V^K`, with unit `e_K`;
- VI.9.4, printed p.201 / PDF p.207: the Proposition is stated with `H(G, K)`-modules `V^K`.

The comparison itself is not printed. It is the standard identification of a bi-`K`-invariant
compactly supported function with its values on cosets, normalized so that `e_K` corresponds to
the unit `δ_K`.

## Published objects used

- `HeckeAlgebra μ`, `HeckeAlgebra.Corner μ K hK` and `Corner.toHeckeAlgebra`. Elements of the
  corner are functions on `G` through `toHeckeAlgebra`. The convolution is
  `(f ∗ g)(x) = ∫ f(y) g(y⁻¹ x) dμ(y)`.
- `heckeAction μ ρ hρ`: the integrated action `f ↦ ∫ f(g) ρ(g) dμ(g)` of `HeckeAlgebra μ` on a
  smooth representation (III.1.3).
- `Langlands.Shimura.LevelHecke.LevelHeckeAlgebra ℂ K`: the `K`-fixed vectors of
  `ℂ[G/K]` (`HeckeSpace ℂ K K`) with convolution `(a ∗ b)(z) = Σ_{yK} a(yK) b(y⁻¹ z)`. It acts on
  `fixedVectors ρ K` through the instance `instModuleFixedVectors`.
- `μ.real (K : Set G)`: the Haar measure of `K`, positive and finite since `K` is compact and
  open.

## The statement

**`LevelHeckeCornerComparisonStatement`.** Let `G` be a t.d. group (Hausdorff, locally compact,
non-archimedean), `μ` a left Haar measure and `K` a compact open subgroup. There is a
complex-linear bijection `e : LevelHeckeAlgebra ℂ K ≃ Corner μ K hK` such that:

1. `e(a ∗ b) = e(a) e(b)`;
2. `e(a)(x) = μ(K)⁻¹ a(xK)` for all `x ∈ G`;
3. for every smooth representation `(ρ, V)`, every `a` and every `w ∈ V^K`,
   `a • w = heckeAction μ ρ hρ (e(a)) w`.

## Formalization choices

- **Normalization.** The factor `μ(K)⁻¹` is forced by 1: the unit `δ_K` of the level algebra goes
  to `μ(K)⁻¹ 1_K = e_K`, the unit of the corner (`normalizedIndicator`). Clause 2 determines `e`,
  so the bijection is canonical.
- **Multiplicativity.** The corner carries only a nonunital ring instance in the Library. So
  `e` is stated as a linear equivalence that preserves products. It then also preserves units, by
  2.
- **Clause 3.** This identifies the `LevelHeckeAlgebra`-module `V^K` used by the published VI.9.4
  statement with the `H(G, K)`-module `V^K` of III.1.5. It is the comparison needed to read that
  statement in the source's terms.

## Why the statement is true

A bi-`K`-invariant test function is constant on the finitely many cosets `xK` of its support.
So `a ↦ μ(K)⁻¹ a` is a linear bijection from left-`K`-invariant finitely supported functions on
`G/K` onto bi-`K`-invariant test functions. For products, the function `y ↦ b(y⁻¹ x K)` is
constant on cosets `yK`, because `b` is left `K`-invariant. Hence
`∫ μ(K)⁻² a(yK) b(y⁻¹ xK) dμ(y) = μ(K)⁻¹ Σ_{yK} a(yK) b(y⁻¹ xK)`. For actions, `w ∈ V^K` gives
`∫ μ(K)⁻¹ a(gK) ρ(g) w dμ(g) = Σ_{gK} a(gK) ρ(g) w`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.Corner` | `HeckeAlgebra.Corner`, `Corner.toHeckeAlgebra`; through its imports `HeckeAlgebra` |
| `Langlands.Representation.Hecke.IntegratedConvolution` | `heckeAction` |
| `Langlands.Shimura.LevelHeckeAlgebra` | `LevelHeckeAlgebra`, `HeckeSpace`, the action on fixed vectors; through its imports `fixedVectors`, `IsSmooth` |
