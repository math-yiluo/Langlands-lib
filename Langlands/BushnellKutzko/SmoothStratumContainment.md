# Fundamental strata in smooth representations of `GL_N(F)`

Module `Langlands.BushnellKutzko.SmoothStratumContainment`, namespace
`Langlands.BushnellKutzko`. It imports `Langlands.BushnellKutzko.StratumExistence`,
`Langlands.BushnellKutzko.NormalizedLevelExistenceProof`,
`Langlands.BushnellKutzko.PureStratumApproximationNonsplitTransfer` and
`Langlands.Representation.Category.Basic`.

The module proves the positive-level part of Bushnell (1987), §3, Theorem 2′, namely
Theorem 2′(ii) and its proof (printed p. 197), for an arbitrary nonarchimedean local field `F` and
an arbitrary complex representation `ρ : Representation ℂ (GeneralLinear n F) W`. It does not
assume that `ρ` is smooth, irreducible or admissible. In place of these assumptions, the
minimum-level result (§4) assumes that some congruence subgroup `U^{l+1}(𝔄(𝓛))` fixes a nonzero
vector of `ρ` and that no `U^1(𝔄(𝓛))` fixes a nonzero vector. The level-zero case,
Theorem 2′(i) (printed p. 196), assumes such a `U^1`-fixed vector and chooses an order of maximal
period. The module does not treat it.

`StratumExistence` proves the same steps for `p`-adic fields and classes of admissible
representations. This module reuses its general-`F` lemmas (`exists_addChar_eigenvector`,
`exists_mem_endFiltration_forall_eq`, `LatticeChain.coordEnd` and its lemmas) and the lemmas of
`LevelAttainingStratum`. It adds the coprimality step of BK93 (8.1.5), printed p. 268, and
the split/nonsplit dichotomy of BK93 (2.3.3), printed p. 58.

Notation: `𝓛` and `𝓜` are `𝒪[F]`-lattice chains in `F^N = Fin n → F`, `e(𝓛) = 𝓛.period`,
`𝔓^k(𝓛) = 𝓛.endFiltration k` and `U^k(𝔄(𝓛)) = 𝓛.unitFiltration k`, a subgroup of
`(Module.End F (Fin n → F))ˣ`. Such a unit acts on `W` through the inverse of
`Matrix.GeneralLinearGroup.toLin`, written `toG` in the Lean file. `ψ_b` is
`elementCharacter (traceCharacter ψ) b`, that is `g ↦ ψ(tr(b(g - 1)))`.

## 1. A character at each level with a fixed vector

`LatticeChain.exists_traceCharacter_eigenvector`. Let `ψ : AddChar F ℂ` be trivial on `𝔭_F`
(`hψ`) and nontrivial on `𝔬_F` (`hψ'`). Let `m ≥ 1`, and let `w ≠ 0` be fixed by `U^{m+1}(𝔄(𝓛))`.
Then there are `b ∈ 𝔓^{-m}(𝓛)` and `v ≠ 0` with `ρ(g) v = ψ_b(g) v` for all `g ∈ U^m(𝔄(𝓛))`.

This is the remark after Bushnell (1987), (3.3), printed p. 196, that a stratum of the
corresponding level occurs in the representation. Here it holds at every level `m ≥ 1` with a
`U^{m+1}`-fixed vector, and the character is written as `ψ_b`, as in the proof of
Theorem 2′(ii), printed p. 197. The proof:

- The `U^{m+1}`-fixed vectors form a subspace `W_f` that contains `w`.
- `W_f` is stable under `U^0(𝔄)`, because `U^0` normalizes `U^{m+1}`.
- Two units of `U^0` that agree modulo `𝔓^{m+1}` act on `W_f` in the same way.
- Choose a basis splitting `𝓛` (`exists_basis_splits_both`). Then
  `z ↦ 1 + coordEnd z` parametrizes `U^m / U^{m+1}` by the finite additive group of matrices
  over the residue field.
- The parametrization is additive modulo `𝔓^{m+1}`. So these operators give a representation of
  that finite abelian group on `W_f`, and `exists_addChar_eigenvector` gives a common eigenvector
  `v` with character `χ`.
- `χ` defines a character of `𝔓^m / 𝔓^{m+1}`. `exists_mem_endFiltration_forall_eq` writes it as
  `x ↦ ψ(tr(b x))` with `b ∈ 𝔓^{-m}`.

## 2. A stratum at a minimal level is fundamental

`LatticeChain.not_isNilpotent_add_of_minimal`. Let `m ≥ 1`, `b ∈ 𝔓^{-m}(𝓛)`, and let `v ≠ 0`
satisfy `ρ(g) v = ψ_b(g) v` on `U^m(𝔄(𝓛))`. Suppose `m · e(𝓜) ≤ l · e(𝓛)` whenever
`U^{l+1}(𝔄(𝓜))` fixes a nonzero vector. In other words, `m / e(𝓛)` is minimal. Then `b + y` is not
nilpotent for any `y ∈ 𝔓^{1-m}(𝓛)`.

This is Bushnell (1987), §3, Theorem 2′(ii), printed p. 197. Suppose `b + y` is nilpotent.
`LatticeChain.exists_latticeChain_of_isNilpotent_add` gives `𝓜` and `l` with the properties
below. It combines Bushnell (1987), §2, Theorem 1, printed p. 192, with the duality step in the
proof of Theorem 2′(ii). The properties are:

- `l · e(𝓛) < m · e(𝓜)`;
- `b ∈ 𝔓^{-l}(𝓜)`;
- `𝔓^{l+1}(𝓜) ⊆ 𝔓^m(𝓛)`.

Then `U^{l+1}(𝔄(𝓜)) ⊆ U^m(𝔄(𝓛))` (`unitFiltration_le_of_endFiltration_le`). On
`U^{l+1}(𝔄(𝓜))` the character `ψ_b` is trivial (`addChar_trace_eq_one_of_mem_one`), so `v` is
fixed by `U^{l+1}(𝔄(𝓜))`. This contradicts minimality.

## 3. Coarser lattice chains

For `d ∣ e(𝓛)`, `LatticeChain.stride 𝓛 d hd hdvd` is the lattice chain `i ↦ L_{d i}`:

- `stride_lattice` gives its lattices;
- `period_stride` gives its period, `e(𝓛) / d`;
- `endFiltration_stride_le` gives `𝔓^{k+1}(stride) ⊆ 𝔓^{dk+1}(𝓛)`.

These hold for any lattice chain over any `O ⊆ K`.

## 4. A minimal level with coprime period

`exists_minimal_fixed_level`. Assume:

- some `U^{l+1}(𝔄(𝓛))` fixes a nonzero vector of `ρ` (`hex`);
- no `U^1(𝔄(𝓛))` does (`hnone`).

Then there are `𝓛`, `m` and `w ≠ 0` with:

- `m ≥ 1`;
- `gcd(m, e(𝓛)) = 1`;
- `w` is fixed by `U^{m+1}(𝔄(𝓛))`;
- `m · e(𝓜) ≤ l · e(𝓛)` whenever `U^{l+1}(𝔄(𝓜))` fixes a nonzero vector.

Proof. Every period divides `N!` (`period_le_card`). So `Nat.find` minimizes
`l · (N! / e(𝓛))`, which is `N!` times the normalized level. `hnone` gives `m ≥ 1`. With
`d = gcd(m, e(𝓛))`, pass to `stride 𝓛 d`. Its period is `e(𝓛) / d`, its level is `m / d`, and these
are coprime. The normalized level is unchanged. `endFiltration_stride_le` with `k = m/d` gives
`U^{m/d+1}(stride) ⊆ U^{m+1}(𝓛)`, so `w` stays fixed. BK93 (8.1.5), printed p. 268, uses
such a coprime pair, and Bushnell (1987), §3, Theorem 2′(ii), printed p. 197, takes the
minimum.

## 5. Split and nonsplit fundamental strata

`Stratum.isNonsplit_of_not_isSplit`. A fundamental stratum `S` over `𝒪[F]` that is not split
(`Stratum.IsSplit`) is nonsplit (`Stratum.IsNonsplit`). This is BK93 (2.3.3), printed p. 58.

Proof. Fix a prime element `ϖ`. The fundamental polynomial `φ_b` is the reduction of the
characteristic polynomial of the fundamental element. It is monic of positive degree
(`PureApproximation.reduceIntegralPolynomial_monic`, `LinearMap.charpoly_natDegree`). If `φ_b`
had two distinct monic irreducible factors, `S` would be split. So
`PureApproximation.exists_eq_pow_of_not_two_factors` writes `φ_b` as a power of one monic
irreducible polynomial, which is the definition of nonsplit.
