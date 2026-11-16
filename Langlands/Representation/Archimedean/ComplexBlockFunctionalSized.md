# The block Jacquet functional with irreducibility only at the block sizes

Lean module: `Langlands.Representation.Archimedean.ComplexBlockFunctionalSized`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. The operator (request
`08a6dcd43c545ecdb45b5e19f96ef9f4`) assigned the Library statement
`ComplexTemperedStandardIrreducibleStatement` (written U below) to Worker 728 (Task 7064), and
asked for supporting lemmas to be staged under Task 7063. This module is one of them, agreed with
Worker 728. It lets an induction on `n` use U at the sizes of the blocks only, so that U at
size `n` can rest on the Langlands-quotient argument for smaller sizes.

`ComplexBlockFunctional.jac_eq_zero_of_proper` (staged module `ComplexBlockFunctional`) assumes
`ComplexBlockFunctional.TiedIrreducible`, the irreducibility of tied principal series of every
size. Its proof uses this only at the sizes `k + 1` of the blocks `k ∈ ks`. This module restates the
vanishing theorem with that weaker hypothesis. It also discharges the two integration statements
with their staged proofs `complexBlockChartIntegrable` (module `ComplexBlockChartIntegralProof`)
and `complexBlockParabolicIntegration` (module `ComplexBlockParabolicIntegrationProof`).

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ`. `U(N)` is `unitaryCompact ℂ N`, with Haar
probability measure `unitaryHaar N`. `IsPhasePower χ e` (`ComplexPartialJacquet`) means
`χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l| = 1` on the unit circle.
`phaseUnit z = z/|z|` (`ComplexGramFormula`). `dim ks`, `BlockOrdered ks e`, `TiedIrreducible`,
`jac ks e p` and `jacKernel` are as in `ComplexBlockFunctional`. In particular `dim [] = 0` and
`dim (k :: ks) = dim ks + (k + 1)`, so the blocks have sizes `k + 1` for `k ∈ ks`. Unprefixed names
below are in the namespace `Langlands.Archimedean.ComplexBlockFunctionalSized`.

## Definitions

* `TiedIrreducibleAt b`: `TiedIrreducible` at the single size `b`. For every phase-power `ψ` with
  exponents `f`, integral phase weights `q` (`ψ_l(u) = u^{q_l}` on the unit circle) and
  `Re f_l = Re f_0` for `l < b`, the `(𝔤𝔩_b(ℂ), U(b))`-module
  `(principalSeriesRep ℂ b ψ, principalSeriesLie ℂ b ψ)` is irreducible.
  `tiedIrreducible_iff : TiedIrreducible ↔ ∀ b, TiedIrreducibleAt b` holds by definition.
* `TemperedIrreducibleAt b`: U at the single size `b`. For every list `ds` of complex characters
  with `ds.length = b` whose exponents all have the same real part, the module
  `(complexStandardRep b ds, complexStandardLie b ds)` is irreducible.
  `temperedIrreducibleAt_of` gives `U → TemperedIrreducibleAt b` for every `b`.

## The statement

`ComplexBlockFunctionalSizedStatement` says the following. Let `ks` be a list of block
parameters, `n = dim ks`. Suppose `TemperedIrreducibleAt (k + 1)` holds for every `k ∈ ks`. Let
`χ` be characters with exponents `e`, given by the conditions `χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}` and
`χ_l(1) = 1`, with `χ_l(u) = u^{p_l}` on the unit circle, and with `BlockOrdered ks e`. Let `W` be
a proper subspace of the `U(n)`-finite functions of `principalSeries ℂ n χ` (some `U(n)`-finite
function of the principal series is not in `W`), stable under right translation by `U(n)` and
under right derivatives. Then `jac ks e p w = 0` for every `w ∈ W`.

The statement has no other hypotheses. The integration statements
`ComplexBlockChartIntegrableStatement` and `ComplexBlockParabolicIntegrationStatement`, which
`ComplexBlockFunctionalStatement` assumes, are discharged by their staged proofs.

It is proved as `Langlands.Archimedean.complexBlockFunctionalSized`.

Provenance. Derived, internal infrastructure: a refinement of `ComplexBlockFunctionalStatement`
that records which sizes of the tempered irreducibility statement its proof uses. No literature
statement is claimed.

## Proof

* `tiedIrreducibleAt_of`: `TemperedIrreducibleAt b → TiedIrreducibleAt b`. Given `ψ`, `f`, `q`,
  take `ds = [characterOfParams (q_i) (f_i) | i < b]`. Its exponents `f_i` have the common real
  part `Re f_0`. The principal series of `ψ` and the standard module of `ds` have the same
  characters (`complexPositionCharacter_ofFn_params`, `principalSeries_congr`). Irreducibility
  transfers by `isIrreducible_kFinite_congr`. This is the argument of
  `ComplexBlockLanglandsQuotient.tiedIrreducible` at one size.
* `jac_eq_zero_sized`: the statement of `ComplexBlockFunctional.jac_eq_zero` with the hypothesis
  `∀ k ∈ ks, TiedIrreducibleAt (k + 1)`. Let `U ≠ 0` be a `(𝔤, K)`-stable space of `U(n)`-finite
  functions of the principal series of `χ⁻¹`, and `h` a `U(n)`-finite function of the principal
  series of `χ` with `∫_{U(n)} u h = 0` for all `u ∈ U`. Then `jac ks e p h = 0`. The proof is the
  induction on `ks` of `jac_eq_zero`.
  * `ks = []`: `GL_0(ℂ)` is trivial, and `∫ u h = u(1) h(1)` with `u(1) ≠ 0` for some `u ∈ U`.
  * `ks = k :: ks'`, `a = dim ks'`: the dual step
    `ComplexBlockDual.integral_restrictBlock_mul_blockPair_eq_zero` needs the irreducibility of
    the principal series of `blockDualChar a χ` on `GL_{k+1}(ℂ)`. This is
    `TiedIrreducibleAt (k + 1)` for the head block, applied to the exponents
    `−(e_{a+l} + a/2)` and weights `−p_{a+l}` (tied by `IsBlockDominant.tie`). The rest of the
    step (`map_restrictBlock`, `blockPair_mem`, the induction hypothesis for `ks'` with the
    hypothesis restricted to `k' ∈ ks'`) is that of `jac_eq_zero`.
* `jac_eq_zero_of_proper_sized`: a proper `(𝔤, K)`-stable `W` lies in `jacKernel`. Apply
  `jac_eq_zero_sized` to the Library annihilator `ComplexJacquetKernel.annihilator W`, which is
  nonzero and `(𝔤, K)`-stable (`annihilator_le`, `annihilator_rightTranslation`,
  `annihilator_rightDerivative`, `annihilator_ne_bot`).
* `complexBlockFunctionalSized`: assemble `IsPhasePower χ e` from the hypotheses (the phase is
  `|u^{p_l}| = 1` on the unit circle) and apply `jac_eq_zero_of_proper_sized` with
  `complexBlockChartIntegrable`, `complexBlockParabolicIntegration` and `tiedIrreducibleAt_of`.
