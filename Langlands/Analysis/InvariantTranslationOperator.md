# Translation operators on classes with invariant representatives

Module `Langlands.Analysis.InvariantTranslationOperator`, namespace
`Langlands.Analysis.InvariantTranslation`. Main definition: `translateCLM`. Its statement form is
`InvariantTranslationStatement`, proved by `invariantTranslation`.

## Statement

Let `H` be a measurable group (measurable multiplication), in an arbitrary universe. Let `μ` be a
measure on `H`, `D ⊆ H`, and `W : H → [0, ∞]` a measurable weight. Write
`weighted μ D W = (μ|_D).withDensity W`. Let `b ∈ H` and `K < ∞`. Let `P` be a predicate on
functions `H → ℂ`, closed under addition, subtraction and complex scalar multiplication, such that

`∫_D ‖f(b g)‖² W(g) dμ ≤ K · ∫_D ‖f(g)‖² W(g) dμ`

for every measurable `f` satisfying `P`. Let `T` be a continuous linear operator on
`L²(weighted μ D W)` such that every `T Fn` has a measurable representative satisfying `P`. Then
there is a continuous linear operator `L` on the same space with:

1. `‖L‖ ≤ (K^{1/2}).toReal · ‖T‖`;
2. for every `Fn` and every measurable representative `h` of `T Fn` satisfying `P`,
   `L Fn = (g ↦ h(b g))` almost everywhere.

In the application, `P` is invariance under `P₀(F)` and `U_J(𝔸)`, `T` is a Harish-Chandra
component or constant-term operator, and `b` is a split-component point. The bound comes from
`AdelicSplitComponentCentralizer` and the weight inequality `W(g) ≤ κ W(b g)`.

## Proof

- `translate_ae_congr`: if two measurable functions in `P` agree almost everywhere for the weighted
  measure, so do their translates by `b`. Apply the bound to their difference, which lies in `P`:
  the weighted `L²` mass of the translate of the difference is at most `K · 0`.
- `eLpNorm_translate_le`: the `L²` norm of the translate is at most `K^{1/2}` times the `L²` norm.
  Rewrite both norms as weighted lower integrals (`lintegral_weighted`) and take square roots.
- `translateLp`: choose a representative `invRep` of `T Fn` in `P` and take the class of its
  translate, which is in `L²` by the previous item.
- `translateLp_ae_of`: by the first item, the class does not depend on the choice of
  representative.
- `translateCLM`: additivity and homogeneity follow from the previous item applied to sums and
  scalar multiples of representatives, which stay in `P`. The norm bound follows from
  `eLpNorm_translate_le` and `‖T Fn‖ ≤ ‖T‖ ‖Fn‖`.

## Provenance

This is an abstract operator-theoretic lemma derived for the proof of Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered
as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §§7.4–7.6 (pp. 215–220). There the
operators `D_α(s)(T_{a_α})` act on the components `f_P` in weighted `L²` spaces. This module
provides the bounded operators "translate by `b` after `T`" on which such polynomials are built. It
does not instantiate them adelically and does not prove any estimate of §7.5.
