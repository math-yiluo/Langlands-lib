# Strata in the fibre of a simple stratum one level up

Fix a simple stratum `T = [𝔄,n,r,γ]`, a field `E` acting on `V` with a
generator mapping to `γ`, and a tame corestriction `s` relative to `E/F`.
A simple stratum `S = [𝔄,n,r−1,β]` with `β − γ ∈ 𝔓^{−r}` has the derived
element `s(β − γ)`. This module follows the proof of (1.8) in
Bushnell–Kutzko 1994, `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
printed pp. 114–115.

## Results

- `mem_endFiltration_restrictScalars` from `RefinementProof`: on a chain over `E` with the
  lattices of `𝔄`, the filtration consists of the `E`-endomorphisms whose
  restriction lies in that of `𝔄` (so `𝔔^k = 𝔓^k ∩ B`).
- `exists_unit_conj_of_derived`: if `s(c_i) ≡ α_i (mod 𝔔^{1−r})` and a
  unit `w` of `𝔅` satisfies `w⁻¹α₁w ≡ α₂`, then `γ + c₁` and `γ + c₂` are
  conjugate modulo `𝔓^{1−r}` by a unit of `𝔄`. The unit `W` of `𝔄`
  induced by `w` commutes with `γ`; `s(W⁻¹c₁W) = w⁻¹s(c₁)w` since `s` is a
  `(B,B)`-bimodule map; hence `s(W⁻¹c₁W − c₂) ∈ 𝔔^{1−r}`, and
  `exists_unit_conj_add_sub_mem` conjugates `γ + W⁻¹c₁W` to `γ + c₂`. This
  replaces the intertwining comparison of (1.9) by a direct conjugation,
  which is the direction used for the labels.
- `isSimple_lower`: `[𝔄,n,r−1,γ]` is simple.
- `elementInvariants_of_derived_null`: if `s(β − γ) ∈ 𝔔^{1−r}`, then
  `F[β]` and `F[γ]` have the same ramification index and residue degree.
  A conjugate of `β` by `U¹(𝔄)` is congruent to `γ` modulo `𝔓^{1−r}`;
  equivalent simple strata have the same invariants (`stratumEquivalence`,
  BK93 (2.1.4)) and so do conjugate ones
  (`PureApproximation.elementInvariants_conj`).
- `elementInvariants_of_derived_simple`: if `s(β − γ)` is congruent
  modulo `𝔔^{1−r}` to the element `α` of a simple stratum `[𝔅,r,r−1,α]`
  over `E` on the lattices of `𝔄`, then
  `e(F[β]|F) = e(E|F) e(E[α]|E)` and `f(F[β]|F) = f(E|F) f(E[α]|E)`
  ((1.12), printed p. 115). The valuation of `β − γ` is exactly `−r`; the
  refinement theorem (`refinement`, BK93 (2.2.8)) gives a simple stratum
  equivalent to `[𝔄,n,r−1,β]` whose invariants are those of `F[γ, α]`,
  computed in `SimpleStratumLabelAdjoin`.
- `exists_simple_of_derived_notMem`, for `E = F[γ]`: if
  `s(β − γ) ∉ 𝔔^{1−r}`, it is congruent modulo `𝔔^{1−r}` to the element
  of a simple stratum `[𝔅,r,r−1,α]`. If `k₀(β,𝔄) = −r`, this is
  `criticalDerivedStratum` (BK93 (2.4.1)(iii)). Otherwise `[𝔄,n,r,β]` is
  simple and equivalent to `[𝔄,n,r,γ]`, so
  `simpleStratumCorestrictionCongruence` (BK93 (2.4.1)(ii)(c)) gives
  `s(β − γ) ≡ −δ` with `δ ∈ E`; then `−δ` has valuation exactly `−r` and
  `PureApproximation.exists_scalar_simple` gives the scalar simple
  stratum.
