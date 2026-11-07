# Renard VI.8.1: coefficient averaging and fixed tensors

Worker 1761 proves the unchanged `FixedTensorComparisonStatement` from
`RenardFamilyStatements` at independent universes `uB`, `uG`, `uV`, `uE`.
The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, VI.8.1, proof of the Proposition, printed p.188 / PDF p.194.
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented proof uses the published finite-orbit averaging over complex
numbers in `Langlands.Compact.CharZero`. Restrict the original coefficient
module along `ℂ → B`. Multiplication by any `b : B` is a complex-linear
intertwiner, so naturality of the finite-orbit mean proves that averaging is
`B`-linear. Its image lies in the compact-open fixed vectors, and it fixes
those vectors pointwise. The resulting `coefficientFixedProjection` splits
the original fixed-submodule inclusion. The auxiliary definitions and lemmas
are intrinsic extensions of published averaging, for the present proof.

The tensor action with trivial first factor is smooth: a pure tensor inherits
a fixing open subgroup from its second factor, and the intersection of two
fixing open subgroups fixes a sum. Naturality of averaging under the map
`v ↦ e ⊗ v` shows that averaging on `E ⊗[B] V` acts as `id ⊗ e_K`.
Tensoring the split inclusion and projection gives a left inverse, hence
injectivity for the natural tensor inclusion. Its range consists of fixed
vectors by tensor induction. Conversely, a fixed tensor is unchanged by
averaging, so applying the tensor projection gives its preimage in
`E ⊗[B] V^K`. This is the inverse described in the source.

The helper result needs only a commutative complex coefficient algebra,
smoothness and a compact open subgroup. The closing theorem keeps all
hypotheses and the exact target of the published statement. No imported
statement or definition is changed, and no axiom is added.
