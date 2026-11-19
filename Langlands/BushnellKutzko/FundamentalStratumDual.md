# A nilpotent representative from triviality on a filtration intersection

`Langlands.BushnellKutzko.FundamentalStratumDual` supplies the linear algebra for the
minimality argument in `FundamentalStratumLevelCore`. It imports `FiltrationCoordinates`,
whose `SplittingBasis` dependency gives a common basis for two chains.

## Nilpotent representative

`LatticeChain.exists_isNilpotent_add` takes two `𝔬_F`-lattice chains `𝓛` and `𝓛''` in
`F^ι` over a nonarchimedean local field `F`, with `ι` finite and a uniformizer `ϖ`.
Write `e` and `e''` for their periods and `𝔓^j(𝓛)` for `𝓛.endFiltration j`. For
`m, m'' ∈ ℤ` the hypotheses are

- `m''·e < m·e''`, or equivalently `m''/e'' < m/e`.
- `b ∈ 𝔓^{-m}(𝓛)`.
- `ψ : AddChar F ℂ` and `s ∈ 𝔬_F` satisfy `ψ(s) ≠ 1`.
- `ψ(tr(b x)) = 1` for every `x ∈ 𝔓^m(𝓛) ∩ 𝔓^{m''+1}(𝓛'')`.

The theorem produces `y ∈ 𝔓^{1-m}(𝓛)` with `b + y` nilpotent. This is the
obstruction to fundamentality in Bushnell–Kutzko (1993), §2.3, printed p. 57
(`bushnell-kutzko-1993-admissible-dual-gln`). Bushnell (1987), Remark (2.9),
printed p. 195, gives a related nilpotent-coset criterion involving a smaller
normalized level (`bushnell-1987-hereditary-orders-gauss-sums`). The trace
hypothesis here is the one obtained by group intertwining in the route of the
operator note, Lemma 4.11(i), printed pp. 15–16
(`operator-numerical-llc-route-2026-11-16`).

## Proof

1. Use `LatticeChain.exists_basis_splits_both` to choose a basis `β` splitting both
   chains. Write `ν` and `ν''` for `𝓛.index hϖ` and `𝓛''.index hϖ`. In
   `FiltrationCoordinates`, `entry β b l k = b_{lk}` and `elementaryEnd β l k t`
   denotes `E_{lk}(t)`, which sends `β_k` to `t β_l` and the other basis vectors
   to zero. The same module supplies the expansion of `b` as the sum of these
   entry endomorphisms, the trace formula `tr(b E_{kl}(t)) = t b_{lk}`, and the
   filtration inequalities for nonzero entries and elementary endomorphisms.
2. Consider an entry `b_{lk}` with `E_{lk}(b_{lk}) ∉ 𝔓^{1-m}(𝓛)`. It is nonzero.
   The entry inequality for `b ∈ 𝔓^{-m}(𝓛)` and failure at the next integer step
   give `e·ord(b_{lk}) = ν(β_k) - ν(β_l) - m`. Since `s` has nonnegative
   valuation, the transposed test endomorphism `x = E_{kl}(s/b_{lk})` lies in
   `𝔓^m(𝓛)`. Its trace pairing with `b` equals `s`, so the triviality hypothesis
   and `ψ(s) ≠ 1` imply `x ∉ 𝔓^{m''+1}(𝓛'')`. Combining this second-chain
   inequality with the first-chain equality and `m''·e < m·e''` gives
   `w(l) < w(k)` for `w(k) = e''·ν(β_k) - e·ν''(β_k)`.
3. Expand `b = z + c`, with `c` the sum of the entry endomorphisms in
   `𝔓^{1-m}(𝓛)`. Take `y = -c`. Each summand of `z` sends `β_k` into the span
   of the basis vectors of weight strictly smaller than `w(k)`.
4. Apply `isNilpotent_of_lt_weight`. Its induction places `z^r β_k` in the span
   of the `β_l` with `w(l) + r ≤ w(k)`. With a nonempty basis, the power at
   `r = max w - min w + 1` therefore vanishes on every basis vector. With an
   empty basis, the endomorphism is already zero by basis extensionality.
