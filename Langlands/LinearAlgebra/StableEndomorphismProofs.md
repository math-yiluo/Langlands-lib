# Stable endomorphisms of arbitrary complex vector spaces: proofs

Author: Worker 277.

This module proves the closed statement targets of
`Langlands/LinearAlgebra/StableEndomorphismStatements.lean`. That file is imported
unchanged. The targets formalize David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.II,
Definition and Lemma (i)–(iv), printed pages 276–278 / PDF pages 282–284
(registered source `renard-2026-representations-groupes-reductifs-padiques`).
The statement Markdown records how they correspond to the source.

All declarations are in the namespace
`Langlands.LinearAlgebra.StableEndomorphism`.

## Exported theorems

| Theorem | Proves exactly |
| --- | --- |
| `stableIffIsCompl` | `StableIffIsComplStatement.{uV}` |
| `stableOfRightExact` | `StableOfRightExactStatement.{uA, uB, uC}` |
| `stableOfLeftExact` | `StableOfLeftExactStatement.{uA, uB, uC}` |
| `powerKernelRangeMonotonicity` | `PowerKernelRangeMonotonicityStatement.{uV}` |
| `adjacentStabilization` | `AdjacentStabilizationStatement.{uV}` |
| `firstStabilizationIndex` | `FirstStabilizationIndexStatement.{uV}` |
| `stableEndomorphism` | `StableEndomorphismStatement.{uV, uA, uB, uC}`, the aggregate, as the conjunction of the six theorems above in order |

Each theorem has the published proposition as its type and adds no hypotheses.
Carriers are arbitrary complex vector spaces in the independent universes `uV`,
`uA`, `uB` and `uC`, and the zero space is allowed. No finite-dimensionality,
countability, nontriviality, chain condition or splitting is assumed.
The exact rows stay one-sided, as published: (ii) uses `range phi = ker psi`
and surjectivity of `psi` only, and (iii) uses injectivity of `phi` and
`range phi = ker psi` only. The two commuting squares are used only through the
pointwise identities `fB (phi a) = phi (fA a)` and `fC (psi b) = psi (fB b)`,
obtained from the published equations by `LinearMap.congr_fun`.
The aggregate theorem, and hence each clause theorem it uses, depends only on
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Elementwise forms of stability

The one-space helpers are stated for `t : Module.End ℂ V`.

- `ker_le_ker_sq` and `range_sq_le_range` give the two trivial inclusions.
  So `stable_iff_le` reduces `Stable t` to `ker (t ^ 2) ≤ ker t` and
  `range t ≤ range (t ^ 2)`.
- `Stable.apply_eq_zero`: if `t` is stable and `t (t x) = 0`, then `t x = 0`.
- `Stable.exists_apply_sq`: if `t` is stable, every `t x` equals `t (t y)` for
  some `y`.
- `Stable.exists_decomp_sq`: if `t` is stable, every `x` equals `k + t (t u)` with
  `t k = 0`. Apply `exists_apply_sq` twice: first `t x = t (t w)`, so
  `x - t w ∈ ker t`, then `t w = t (t u)`. This uses only the range half of
  stability.

## Lemma (i)

`stable_iff_isCompl` follows the source proof. It uses Mathlib's
`Submodule.disjoint_def` and `Submodule.codisjoint_iff_exists_add_eq`, which
describe `IsCompl` of actual submodules.

- Disjointness: if `t w ∈ ker t`, then `t (t w) = 0`, so `t w = 0` by
  `Stable.apply_eq_zero`.
- Codisjointness: write `t x = t (t w)`; then `x = (x - t w) + t w`, with
  `x - t w ∈ ker t`.
- Conversely, `t (t x) = 0` puts `t x` in `ker t ⊓ range t = ⊥`. For `t w`,
  decompose `w = k + t z` with `t k = 0`; then `t w = t (t z)`.

## Lemma (ii)

`stable_of_rightExact` proves both inclusions of `stable_iff_le` for `fC`.
It does not pass through (i).

- Kernel: let `fC (fC c) = 0`. Choose `b` with `psi b = c`, using surjectivity.
  Then `psi (fB (fB b)) = 0`, so exactness gives `fB (fB b) = phi a`.
  Decompose `a = k + fA (fA u)` with `fA k = 0` by
  `Stable.exists_decomp_sq` for `fA`. Then
  `phi k = fB (fB (b - phi u))`. Since `fB (phi k) = phi (fA k) = 0`,
  `Stable.apply_eq_zero` for `fB` gives `phi k = 0`. Applying it again gives
  `fB (b - phi u) = 0`, so `fB b = phi (fA u)`. Hence
  `fC c = psi (fB b) = psi (phi (fA u)) = 0`, since `range phi = ker psi`.
  This is the source's reduction to `ker fC ∩ Im fC = 0`, carried out
  elementwise.
- Range: for `c = psi b`, write `fB b = fB (fB y)`. Then
  `fC c = psi (fB (fB y)) = fC (fC (psi y))`.

## Lemma (iii)

`stable_of_leftExact` again proves the two inclusions for `fA`.

- Kernel: if `fA (fA a) = 0`, then `fB (fB (phi a)) = 0`, so
  `fB (phi a) = phi (fA a) = 0`, and `fA a = 0` by injectivity of `phi`.
- Range: decompose `phi a = k + fB (fB b)` with `fB k = 0`. Applying `psi`
  gives `psi k + fC (fC (psi b)) = 0`. Also `fC (psi k) = psi (fB k) = 0`, so
  `fC (fC (fC (psi b))) = 0`. Two applications of `Stable.apply_eq_zero` for `fC`
  give `psi (fB b) = fC (psi b) = 0`. So exactness gives `fB b = phi a₁`.
  Then `k = phi (a - fA a₁)`, and `phi (fA (a - fA a₁)) = fB k = 0`.
  Injectivity gives `fA a = fA (fA a₁)`. This replaces the source's auxiliary
  claim (C.II.1) with the direct computation above.

## Lemma (iv)

Write `N_k = ker (t ^ k)` and `I_k = range (t ^ k)` for all `k : ℕ`, including
`k = 0`.

- `ker_pow_monotone` is `(LinearMap.iterateKer t).monotone`. `range_pow_antitone`
  is `(LinearMap.iterateRange t).monotone`, whose codomain is the order dual.
  `powerKernelRangeMonotonicity` packages them without eventual stability.
- `ker_pow_eq_of_le` applies Mathlib's `Module.End.ker_pow_constant` over the
  division ring `ℂ`. That lemma has no finite-dimensionality hypothesis; it
  propagates `N_k = N_(k+1)` to every `m ≥ k`. `range_pow_eq_of_le` is the
  analogous range propagation, by induction using
  `LinearMap.iterateRange_succ` (`I_(n+1)` is the image of `I_n` under `t`).
- `EventuallyStable.exists_constant`: from a positive `n` with `t ^ n` stable,
  `pow_mul` turns the stability equalities into `N_n = N_(n·2)` and
  `I_n = I_(n·2)`. Monotonicity squeezes `N_(n+1)` and `I_(n+1)` between them,
  so both chains are constant from `n` on.
- `range_eq_of_ker_eq`: assume eventual stability, with both chains constant
  from `M`, and `N_k = N_(k+1)`. For `t ^ k v`, constancy of the ranges gives
  `t ^ (k+M) v = t ^ (k+M+1) w`. Then `v - t w ∈ N_(k+M) = N_k`, so
  `t ^ k v = t ^ (k+1) w`.
- `ker_eq_of_range_eq`: assume `I_k = I_(k+1)` and let `t ^ (k+1) v = 0`. Then
  `I_k = I_(k+M)` gives `t ^ k v = t ^ (k+M) w`, and `t ^ (k+M+1) w = 0`.
  Since `N_(k+M+1) = N_M = N_(k+M)`, it follows that `t ^ k v = 0`.
- `adjacentStabilization` combines the two implications into the adjacent
  equivalence. Either adjacent equality gives the kernel equality, hence both
  equalities, and the two propagation lemmas give constancy for every `m ≥ k`.
- `firstStabilizationIndex` takes `k₀ = Nat.find` of the existence of an index
  with `N_k = N_(k+1)`. Existence comes from `EventuallyStable.exists_constant`.
  `Nat.find_spec` and the propagation lemmas give constancy of both chains from
  `k₀`. For `j < k₀`, `Nat.find_min` gives `N_j ≠ N_(j+1)`. An equality
  `I_j = I_(j+1)` would give `N_j = N_(j+1)` by `ker_eq_of_range_eq`, so it
  fails as well. The index `k₀` may be zero.

This route avoids the source's quotient spaces `E_k = N_(k+1)/N_k`,
`F_k = I_k/I_(k+1)` and its five-term exact sequence. It therefore does not
formalize those auxiliary constructions or assertions of the printed proof.
Those obligations, the adapter to the book's possibly nonunital algebra-module
setting, and the finite-localization proposition on printed page 279 /
PDF page 285 all remain outside this module.

## Imports

The module imports only the unchanged statement module and
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`, which declares
`Module.End.ker_pow_constant`.
