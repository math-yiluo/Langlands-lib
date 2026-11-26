# Siegel sets and truncation for every compact Iwasawa subgroup

Module `Langlands.Global.ArthurSiegelSetsIwasawaStatement`, namespace
`Langlands.Global.ArthurTruncation`. The objects are those of
`Langlands.Global.ArthurSiegelSets`, `Langlands.Global.ArthurTruncation` and the predicates of
`Langlands.Global.ArthurSiegelSetsStatement` and `Langlands.Global.ArthurTruncationStatement`
(see their Markdown, in particular "Common hypotheses" and "Predicates"). The module defines one
predicate of a compact subgroup, `IsSiegelReductionLemma`, and states five propositions and
their conjunction. Each proposition asserts one of the predicates for **every** compact subgroup
`K` of `G(𝔸)` with `P_0(𝔸)K = G(𝔸)` (`hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K`);
the constants (the regularity bounds `c`, the Siegel data `ω`, `T_1` of the covering) may depend
on `K`. The predicates `IsSiegelCovering`, `IsSiegelPartition`, `IsRelativeSiegelPartition`,
`IsTruncationRapidDecay` and `IsTruncationIdempotent` are used as defined in those modules. The
module proves none of the statements.

## Sources

- J. Arthur, *A trace formula for reductive groups I* (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I`, §6, printed pp.941–942 (PDF pp.31–32): the
  choice of `ω`, `T_0` with `G(𝔸) = P_1(ℚ) S^{P_1}(T_0, ω)` for every `P_1` (p.941), the result
  from reduction theory quoted before Lemma 6.4 (p.941, from the proof of Langlands, *On the
  functional equations satisfied by Eisenstein series*, Lemma 2.12), and Lemma 6.4 with its proof
  (pp.941–942); Lemma 5.1 (p.936, PDF p.26) for the count of rational cosets.
- J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):
  Theorem 8.1 (p.37), Lemma 8.2 (p.38) with its geometric restatement (p.39), (8.1) (p.40,
  derived on p.41), Proposition 13.1(a),(b) (pp.68–69), Proposition 13.2(a) (p.71).
- J. Arthur, *A trace formula for reductive groups II* (1980), registered as
  `arthur-1980-trace-formula-reductive-groups-II` (PDF page = printed page − 85), §1: Lemma 1.1
  with its proof (pp.89–91; Proposition 13.1(a) of Arthur 2005, which calls this paper [A4]) and
  Lemma 1.4 with the estimates before it and its proof (pp.92–97, PDF pp.7–12; the statement
  begins on p.95; Proposition 13.2 of Arthur 2005).

## Common hypotheses

All five statements have the hypotheses of the statements of
`Langlands.Global.ArthurTruncationStatement`: a number field `F`, a group scheme `G` over `F`,
affine and locally of finite type, connected reductive (`hG`), a maximal split torus
`i : T → G` (`hi`) and a generic cocharacter `ν` (fixing `P_0`). They are followed by a subgroup
`K` with `hK` (compact and `P_0(𝔸)K = G(𝔸)`, with no maximality or further condition), the
bijectivity `hρ` used by the height `H_0 = height hi hK hρ` defined with `K` and, where the
predicate needs it, reflection data `D`. Standard parabolic subgroups `P` are indexed by
`Δ_0^P = S ∈ (simpleFinset ν hG hi).powerset`. "Suitably regular" `T ∈ 𝔞_0` is `β(T) > c` for
every `β ∈ Δ_0` (`simpleRelativeRoots i ν`), where `c` depends on the data quantified before it.

## Predicate

### `IsSiegelReductionLemma hG hi hK hρ` (Arthur 1978, p.941)

For every compact factor data `C` with `C.compactSubgroup = K` (`ω = Ω_N Ω_M`) and every
`T_1 ∈ 𝔞_0` there is `c` such that for every `T` with `β(T) > c` for every `β ∈ Δ_0`, every
pair of standard parabolic subgroups `P_1 ⊆ P` (`Δ_0^{P_1} = S₁ ⊆ SP = Δ_0^P`), every
`x ∈ G(𝔸)` and every `δ ∈ P(F)` (the image `parabolicRationalImage` of the rational points of
`Standard.parabolicHom i ν SP` in `G(𝔸)`): if `x` and `δx` belong to the Siegel set
`S^P(T_1, ω) = siegelSet hi hK hρ C SP T₁` and `α(H_0(x) − T) > 0` for every
`α ∈ Δ_0^P ∖ Δ_0^{P_1}`, then `δ ∈ P_1(F)`.

**Source reading.** On p.941 Arthur states, for a suitably regular `T`, parabolic subgroups
`P_1 ⊂ P`, `x ∈ G(𝔸)` and `δ ∈ P(ℚ)` with `α(H_0(x) − T) > 0` for all `α ∈ Δ_0^P ∖ Δ_0^{P_1}`,
that `δ ∈ P_1(ℚ)`; the printed premise is that `x` and `δx` belong to `S^{P_1}(T_0, ω)`. The
predicate uses `S^P(T_1, ω)`, the Siegel set in which Arthur places both points when he applies
the result in the proof of Lemma 6.4 (p.942: "`δ_i x` belongs to `S^P(T_0, ω)`. The reduction
theoretic result just quoted now implies …"). The printed premise cannot be the intended one:
for `G = SL₂` over `ℚ`, `P = G`, `P_1 = P_0`, the standard `K` and `ω ∋ 1`, the Siegel set
`S^{P_0}(T_0, ω) = ω A_0(ℝ)^0 K` has no chamber condition. With `a_t = diag(e^t, e^{−t})` at the
real place and `w` the rational Weyl representative with rows `(0, −1)` and `(1, 0)`, which lies
in `K`, both `a_t` and `w a_t = a_{−t} w` lie in it, `α(H_0(a_t) − T) > 0` for large `t`, and
`w ∉ P_0(ℚ)`. With `S^P` the chamber condition `α(H_0(w a_t) − T_1) > 0` fails for large `t`.

The predicate is stated over a number field, for the Siegel sets of the Library (the ordered
products `Ω_N Ω_M a K` with `β(H_0(a) − T_1) > 0` for `β ∈ Δ_0^P`), with `T_1` in place of
Arthur's `T_0`. Arthur quotes the result for the `ω`, `T_0` fixed by the covering property; the
predicate asserts it for all compact factor data and all `T_1`, with `c` chosen after them. This
case reduces to the case of covering data: the Siegel sets increase when `Ω_N` and `Ω_M` are
enlarged and when the values `β(T_1)`, `β ∈ Δ_0`, are lowered. So any `(ω, T_1)` and given
covering data `(ω', T_1')` for `K` are contained in a pair with compact factors `Ω_N ∪ Ω_N'`,
`Ω_M ∪ Ω_M'` and a threshold `T_1''` with `β(T_1'') ≤ min(β(T_1), β(T_1'))` for all `β ∈ Δ_0`
(such a point exists as the simple roots are linearly independent); that pair again has
the covering property, and the bound `c` for it serves for `(ω, T_1)`.

## Statements

### `IwasawaSiegelCoveringStatement`

For every such `K` there are compact factor data `C` with `C.compactSubgroup = K` and
`T_1 ∈ 𝔞_0` with `IsSiegelCovering hG hi hK hρ C T₁`: `G(𝔸) = P_1(F) S^{P_1}(T_1, ω)` for every
standard `P_1`, with one pair `(ω, T_1)` for all `P_1`. Arthur 1978, p.941: "By the properties of
Siegel sets we can fix `ω` and `T_0` so that for any `P_1`, `G(𝔸) = P_1(ℚ) S^{P_1}(T_0, ω)`"; for
`P_1 = G` it is the covering of Arthur 2005, Theorem 8.1 (Borel, Harish-Chandra).

### `IwasawaSiegelReductionStatement`

`IsSiegelReductionLemma hG hi hK hρ` for every such `K`.

### `IwasawaSiegelPartitionStatement`

`IsSiegelPartition hG hi D hK hρ ∧ IsRelativeSiegelPartition hG hi D hK hρ` for every such `K`
and all `D` (Arthur 2005, Lemma 8.2 and (8.1); Arthur 1978, Lemma 6.4). In words:

- *Global partition (Lemma 8.2).* For all compact factor data `ω` with the compact subgroup `K`
  and all `T_1` with `G(𝔸) = G(F) S^G(T_1, ω)` there is `c` such that for every `T` with
  `β(T) > c` for all `β ∈ Δ_0` and every `x ∈ G(𝔸)`: for each standard `P` only finitely many
  `δ ∈ P(F)\G(F)` have `F^P(δx, T) τ_P(H_P(δx) − T) ≠ 0`, and the sum of these terms over all
  standard `P` and all `δ ∈ P(F)\G(F)` is `1`. Each term is `0` or `1`, so exactly one pair
  `(P, δ)` contributes. The shift by `T` in `τ_P` is that of Arthur's geometric restatement
  (p.39); see the Markdown of `ArthurSiegelSetsStatement`.
- *Relative partition ((8.1), Lemma 6.4).* For all `ω` with the compact subgroup `K` and all
  `T_1` with `IsSiegelCovering` there is `c` such that for every `T` with `β(T) > c` for all
  `β ∈ Δ_0`, every standard `P` and every `x ∈ G(𝔸)`: for each `P_1` with `P_0 ⊆ P_1 ⊆ P` only
  finitely many `δ ∈ P_1(F)\P(F)` have `F^{P_1}(δx, T) τ_{P_1}^P(H_{P_1}(δx) − T) ≠ 0`, and the
  sum of these terms over all such `P_1` and `δ` is `1`; again exactly one pair `(P_1, δ)`
  contributes.

Arthur's proof of Lemma 6.4 (pp.941–942) uses, besides the covering hypothesis, only the
reduction-theoretic result of `IsSiegelReductionLemma` (with `S^P`, as above), the combinatorial
Lemma 6.3, the fact that `H_{P_1}(x)` is the projection of `H_0(x)` to `𝔞_{P_1}` and the
invariance of `H_{P_1}` under left translation by `P_1(F)`; all of these hold for every `K` of
the class.

### `IwasawaTruncationIdempotentStatement`

`IsTruncationIdempotent hG hi D hK hρ` for every such `K` and all `D` (Arthur 2005,
Proposition 13.1(a),(b); Arthur 1980, Lemma 1.1 and Corollary 1.2). In words: there is `c` such
that for every `T` with `β(T) > c` for all `β ∈ Δ_0` and every function `φ` on `G(𝔸)` that is
measurable, bounded on compact sets and left `G(F)`-invariant (`IsLocallyBoundedInvariant`, the
class `B_loc`):

- (a) for every standard `P_1` and every `x ∈ G(𝔸)`, if `ϖ(H_0(x) − T) > 0` for some
  `ϖ ∈ Δ̂_{P_1}` (the weights `ϖ_β`, `β ∈ Δ_0 ∖ Δ_0^{P_1}`), then the constant term
  `∫_{N_1(F)\N_1(𝔸)} (Λ^T φ)(n x) dn` vanishes;
- (b) `Λ^T(Λ^T φ) = Λ^T φ`.

### `IwasawaTruncationRapidDecayStatement`

`IsTruncationRapidDecay hG hi D hK hρ` for every such `K` and all `D` (Arthur 2005,
Proposition 13.2(a), in the restricted form explained in the Markdown of
`ArthurSiegelSetsStatement`; Arthur 1980, Lemma 1.4). In words: for every closed matrix
representation `rho` of `G` (defining the height `‖x‖`) and every smooth structure there is `c`
such that for every `T` with `β(T) > c` for all `β ∈ Δ_0` and every finite plot-smooth left
`G(F)`-invariant function `f` with uniformly moderate growth, `Λ^T f` decreases faster than every
inverse power of the height on every Siegel set of `K`: for all compact factor data `ω` with the
compact subgroup `K`, all `T_1` and all `n` there is `B` with `|Λ^T f(x)| ≤ B ‖x‖^{−n}` for
`x ∈ S^G(T_1, ω) ∩ G(𝔸)^1`. The bound `c` comes before the Siegel set on which the decay is
measured; only `B` depends on that Siegel set and on `n`.

### `ArthurSiegelSetsIwasawaStatement`

The conjunction of the five statements.

## Why every compact Iwasawa subgroup

Arthur works with one "suitable" maximal compact subgroup `K` (Arthur 2005, p.24), admissible
relative to `M_0` in the sense of Arthur 1981, pp.9–10; the Markdown of
`ArthurTruncationStatement` ("The compact subgroup") explains why admissibility cannot be stated
with the Library's present objects. `ArthurSiegelSetsStatement` and
`TruncationProjectionStatement` therefore assert that one `K` satisfies the predicates. The
statements of this module are the corresponding assertions for every compact `K` with
`P_0(𝔸)K = G(𝔸)`, the class for which `ArthurTruncationStatement` already states finiteness
(`TruncationFinitenessStatement`), Proposition 13.1(c) (`TruncationSelfAdjointStatement`) and
Proposition 13.3 (`TruncationCancellationStatement`). This is a derived formulation, stronger
than Arthur's results for his `K`: the sources prove the results for an admissible `K`, and no
proof for a general `K` is given here. It is the expected one for the following reasons. Below,
`K_0` denotes an admissible subgroup.

- *Heights of two such subgroups differ by a bounded amount.* If `K'` is another subgroup of the
  class and `g = pk` with `p ∈ P_0(𝔸)`, `k ∈ K`, then `H_{K'}(g) = H_K(g) + H_{K'}(k)`, and
  `H_{K'}` is bounded on the compact set `K` (see the Markdown of `ArthurTruncationStatement`,
  "Bounded difference"). Likewise `H_K(xy) − H_K(x)` is bounded for `y` in a compact set.
- *Where the constants enter.* In Arthur 1978, §6 and Arthur 1980, §1, `K` enters through its
  compactness, the decomposition `G(𝔸) = P_0(𝔸)K`, the right `K`-invariance of `H_0` and
  inequalities between heights. For a general `K` these inequalities hold up to constants
  depending on `K`, which the regularity of `T` absorbs. Every statement chooses its regularity
  bound `c` after `K`; in the reduction lemma and the two partitions also after the Siegel data
  `ω`, `T_1` on which they are evaluated; in the idempotence statement no Siegel data occur; in
  the rapid-decay statement `c` comes after `rho` and the smooth structure but before the Siegel
  set on which decay is measured (see the last item). The exact identities (Lemma 6.4, (8.1), the
  vanishing in Lemma 1.1) come from exact combinatorial identities (Arthur 1978, Proposition 1.1
  and Lemma 6.3) applied to the heights, not from exact properties of `K`.
- *Lemma 1.1 of Arthur 1980.* The proof (p.91) writes
  `s⁻¹(H_0(w_s n^* x) − T) = H_0(x) − T + s⁻¹H_0(w_s v w_s⁻¹) + (T − s⁻¹T)` with `v ∈ N_0(𝔸)`,
  and concludes from the facts that, for `ϖ ∈ Δ̂_0`, `ϖ(s⁻¹H_0(w_s v w_s⁻¹))` is nonnegative and
  `ϖ(T − s⁻¹T)` is positive. For a general `K` the decomposition holds with `H_0(w_s v)` in place
  of `H_0(w_s v w_s⁻¹)`, since `H_0(qz) = H_0(q) + H_0(z)` for `q ∈ P_0(𝔸)`, and
  `ϖ(s⁻¹H_0(w_s v))` is bounded below by a constant `−c_K` (bounded difference of heights, and
  right translation by the finitely many `w_s` changes `H_0` by a bounded amount). When
  `sϖ ≠ ϖ`, `ϖ(T − s⁻¹T) = (ϖ − sϖ)(T)` is a nonzero combination with nonnegative coefficients
  of the values `β(T)`, `β ∈ Δ_0`, and exceeds `c_K` for `T` regular enough. When `sϖ = ϖ`, `s`
  lies in the Weyl group of the Levi component of the maximal parabolic subgroup `P_ϖ` attached
  to `ϖ`, so `w_s v ∈ P_ϖ(𝔸)`, and `ϖ(s⁻¹H_0(w_s v)) = ϖ(H_{P_ϖ}(w_s v)) = 0` for every `K` of
  the class (`w_s` is rational, `v` is unipotent); there `ϖ(T − s⁻¹T) = 0` and the conclusion
  `ϖ(H_0(x) − T) ≤ 0` holds exactly as in Arthur's argument (Arthur 2005, p.68, notes that the
  strict inequality in the statement of Lemma 1.1 should be `≤`). Part (b) of Proposition 13.1
  follows from part (a) by the definition of `Λ^T` alone (Arthur 1980, Corollary 1.2; Arthur
  2005, p.69).
- *The reduction-theoretic lemma.* For a highest weight vector `v_ϖ` of a rational
  representation `Λ` of `G` with highest weight a multiple `dϖ`, the norm `‖Λ(x)⁻¹ v_ϖ‖` is
  comparable to `e^{−dϖ(H_0(x))}`, with constants given by the compact set `K`; the argument
  from reduction theory uses only such estimates.
- *Covering transfers between such subgroups.* If `K'` admits Siegel covering data and
  `K' ⊆ C K` with `C ⊆ P_0(𝔸)` compact (the orbit map `P_0(𝔸) → G(𝔸)/K` is open, so the compact
  set `K'` is covered by finitely many sets `pUK` with `U` a compact neighbourhood of `1` in
  `P_0(𝔸)`). Writing the elements of `C` in `N_0(𝔸) M_0(𝔸)^1 A_0(ℝ)^0` and using
  `N_0(𝔸) = N_0(F) Ω` with `Ω` compact, the pieces of `C` are absorbed into `N_0(F) ⊆ P_1(F)`, a
  larger compact `Ω_M` and a shift of `T_1`, which gives covering data for `K`.
- *Rapid decay (Arthur 1980, pp.92–97).* Fix covering data `(ω, T_1)` for `K` once, and take `c`
  at least the bound of the relative partition for these data. Arthur's argument then runs as
  follows for `K`. (i) By the relative partition and Proposition 1.1 of Arthur 1978, `Λ^T φ(x)`
  is the sum over `P_1 ⊆ P_2` and `δ ∈ P_1(F)\G(F)` of
  `F^{P_1}(δx, T) σ_{P_1}^{P_2}(H_0(δx) − T) φ_{P_1,P_2}(δx)`, where `φ_{P_1,P_2}` is an
  alternating sum of constant terms along the parabolic subgroups between `P_1` and `P_2` (p.92).
  (ii) For a nonzero term, after left translation of `δ` by an element of `P_1(F)`,
  `δx = n^* n_* m a k` with `n^* ∈ N_{P_2}(𝔸)`, `n_* ∈ N_{P_1}(𝔸) ∩ M_{P_2}(𝔸)` and
  `m ∈ M_{P_1}(𝔸)^1` in fixed compact sets (depending on `ω`, `T_1` and `T`),
  `a ∈ A_{P_1}(ℝ)^0` with `σ_{P_1}^{P_2}(H_0(a) − T) ≠ 0`, and `k ∈ K` (p.92). Since
  `φ_{P_1,P_2}` is left `N_{P_2}(𝔸)`-invariant, `φ_{P_1,P_2}(δx) = φ_{P_1,P_2}(a c)` with
  `c = (a⁻¹ n_* a) m k` (p.93). The roots of `A_{P_1}` on `N_{P_1} ∩ M_{P_2}` are positive
  combinations of the roots in `Δ_{P_1}^{P_2}`, which are positive on `H_0(a) − T` in the support
  of `σ_{P_1}^{P_2}` and hence on `H_0(a)` for `T` regular; so `a⁻¹ n_* a` stays in a compact
  set, and `c` lies in a compact subset of `G(𝔸)^1` given by these compact sets and the compact
  set `K`. For the norms, `n^*` is kept as a left factor. The norm `‖·‖` of
  `IsRapidlyDecreasing` is the source norm `RepresentationGrowth.adelicSourceNorm`; the
  submultiplicative height `adelicHeight` is `κ ‖·‖` with the fixed scale
  `κ = N^{∑_v mult(v)}` over the infinite places (`adelicHeight_eq_scalar_mul_sourceNorm`), and
  `adelicHeight_mul_le` gives `‖gh‖ ≤ κ ‖g‖ ‖h‖`. Applied twice,
  `‖δx‖ ≤ κ² ‖n^*‖ ‖a‖ ‖c‖`, with `n^*` in a compact set; the factor `κ²` goes into the
  constant `B`. (Arthur uses a submultiplicative height, Arthur 1978, p.919 and Arthur 2005,
  (13.2), for which the estimate holds without `κ`.) (iii) The Fourier expansion of `φ_{P_1,P_2}` along the unipotent radicals and the
  estimate of `Ad(c)⁻¹ Y_I^n` by finitely many elements `X_i` of the enveloping algebra
  (pp.93–95) use `c` only through the compactness of the set in which it lies; the bound of `‖a‖`
  by a fixed power of `e^{β_I(H_0(a))}` (p.96) involves only the point `a` of the positive torus.
  (iv) Arthur uses `‖γx‖^{−N_1} ≤ c_1 ‖x‖^{−N_1}` for `γ ∈ G(F)` and `x` in the Siegel set on
  which the decay is measured (p.96). For a Siegel set `S^G(T_1', ω')` of `K`, write `x = yk`
  with `y ∈ Ω_N' Ω_M' A_0(ℝ)^0` in the chamber and `k ∈ K`; then `y` lies in the Siegel set of
  `K_0` with the same `ω'`, `T_1'`, for which the inequality holds, and multiplying `y` and `γy`
  on the right by `k` changes their norms by factors bounded in terms of the compact set `K`
  (`‖zk‖ ≤ κ ‖z‖ ‖k‖` and `‖z‖ ≤ κ ‖zk‖ ‖k⁻¹‖`, with `‖k‖` and `‖k⁻¹‖` bounded on `K`).
  (v) The number of nonzero terms `F^{P_1}(δx, T) σ_{P_1}^{P_2}(H_0(δx) − T)`,
  `δ ∈ P_1(F)\G(F)`, is at most `∑_{δ ∈ P_1(F)\G(F)} τ̂_{P_1}(H_0(δx) − T)`, since each such term
  is the characteristic function, at `δx`, of a subset of
  `{y : ϖ(H_0(y) − T) > 0, ϖ ∈ Δ̂_{P_1}}` (p.96). Arthur 1978, Lemma 5.1 (p.936) bounds
  `∑_{δ ∈ P(F)\G(F)} τ̂_P(H_P(δx) − X)` by `c (‖x‖ e^{‖X‖})^N` for all `x ∈ G(𝔸)^1` and
  `X ∈ 𝔞_P`; for the norm-one points `x` at which the decay is tested this gives the bound
  `C_2 ‖x‖^{N_2}` of the majorant (p.97). For `K`, each of the finitely many weights
  `ϖ ∈ Δ̂_{P_1}` changes by at most a constant on `H_0(δx)` when `H_{K_0}` replaces `H_K`, so
  `τ̂_{P_1}(H_K(δx) − T) ≤ τ̂_{P_1}(H_{K_0}(δx) − T')` with `T' = T − X` for a fixed `X`, and
  Lemma 5.1 for `K_0` applies with the projection of `T'` to `𝔞_{P_1}`, on which `τ̂_{P_1}`
  depends. (vi) Arthur then
  takes `N_1 = N' + N_2` and chooses `n`, the `X_i` and the differentiability order accordingly
  (p.97). The constants of (ii)–(v) depend on `K`, on the fixed `(ω, T_1)`, on `T` and on the
  Siegel set on which the decay is measured; they enter `B`, which is chosen after all of these,
  and not `c`. The predicate concerns individual functions with uniformly moderate growth; it is
  the case of a one-point measure space in Lemma 1.4.

`ArthurSiegelSetsStatement` asks for one compact subgroup `K` with `hK` that is in addition
maximal compact (`IsMaximalCompactSubgroup`) and satisfies
`AdelicSiegelFactors.IsPositiveTorusCompatible` for every actual Siegel setup, and that admits
covering data and satisfies `IsTruncationIdempotent`, `IsSiegelPartition`,
`IsRelativeSiegelPartition` and `IsTruncationRapidDecay` for all `D` and `hρ`. For any `K` with
`hK` the last conditions are given by the covering, partition, idempotence and rapid-decay
statements of this module; so these four statements, together with the existence of a maximal
compact, positive-torus compatible `K` with `hK`, imply `ArthurSiegelSetsStatement`.

## Provenance

Source: Arthur 1978, §6, pp.941–942; Arthur 2005, Theorem 8.1, Lemma 8.2, (8.1), Propositions
13.1(a),(b) and 13.2(a); Arthur 1980, Lemmas 1.1 and 1.4. Derived formulation: the assertions for
every compact subgroup `K` with `P_0(𝔸)K = G(𝔸)`, with constants depending on `K`, as explained
in "Why every compact Iwasawa subgroup"; the predicate `IsSiegelReductionLemma` restates the
reduction-theoretic result of Arthur 1978, p.941, for the Library's Siegel sets, with the Siegel
set `S^P` of its application on p.942 in place of the printed `S^{P_1}` (see "Source reading"),
for all compact factor data and all `T_1`.
