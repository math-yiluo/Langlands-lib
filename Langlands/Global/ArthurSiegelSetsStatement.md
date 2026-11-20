# The partition lemma and the rapid decrease of truncated functions

Module `Langlands.Global.ArthurSiegelSetsStatement`, namespace
`Langlands.Global.ArthurTruncation`. Worker 128, Task 5536, item 3 (second unit). The objects are
those of `Langlands.Global.ArthurSiegelSets` and `Langlands.Global.ArthurTruncation` (see their
Markdown). The module defines four predicates of one compact subgroup `K`: `IsSiegelCovering`,
`IsSiegelPartition`, `IsRelativeSiegelPartition` and `IsTruncationRapidDecay`. It states one
proposition, `ArthurSiegelSetsStatement`, which asserts that some `K` satisfies them together
with the predicate `IsTruncationIdempotent` of `Langlands.Global.ArthurTruncationStatement`. It
proves none of them.

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):
  §4, p.24 (the choice of `K`), Theorem 8.1 (p.37), Lemma 8.2 (p.38) with its geometric
  restatement (p.39), (8.1) (pp.40–41), Proposition 13.2 (p.71), with the definitions of p.70.
- J. Arthur, *A trace formula for reductive groups I* (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I`, §6, printed pp.941–942: the choice of `ω` and
  `T_0` with `G(𝔸) = P_1(ℚ) S^{P_1}(T_0, ω)` for every `P_1`, Lemma 6.4 and its proof.
- J. Arthur, *The trace formula in invariant form* (1981), registered as
  `arthur-1981-trace-formula-invariant-form`, §1, pp.9–10: maximal compact subgroups admissible
  relative to `M_0` and their properties (i)–(iii).
- Arthur 2005 sketches the proof of Proposition 13.2 (pp.71–73) and identifies it as that of
  Lemma 1.4 of his reference [A4]; that paper is not used here.

## Common hypotheses

The data are those of `Langlands.Global.ArthurTruncationStatement` (see its Markdown, "Common
hypotheses"): a number field `F`, a connected reductive `G` (`hG`), a maximal split torus
`i : T → G` (`hi`), a generic `ν` (fixing `P_0`), reflection data `D`, and the bijectivity `hρ`
of `ArthurParabolicSpaces.restrictToTorus F i ν ∅` used by the height. Each predicate takes in
addition a subgroup `K` with `hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` (compact and
`P_0(𝔸)K = G(𝔸)`); `H_0 = height hi hK hρ` is the height defined with `K`. Standard parabolic
subgroups `P` are indexed by `Δ_0^P = S ∈ (simpleFinset ν hG hi).powerset`. "Suitably regular"
`T ∈ 𝔞_0` is `β(T) > c` for every `β ∈ Δ_0` (`simpleRelativeRoots i ν`), with `c` depending on
all the data before it.

## The compact subgroup

The Siegel sets `S^P(T_1, ω) = ω A_0(ℝ)^0(T_1) K`, the functions `F^P(x, T)`, the height `H_0`
and the operator `Λ^T` all depend on `K`. Arthur proves Lemma 8.2, (8.1) and Proposition 13.2
for "a suitable maximal compact subgroup `K`" (2005, p.24), which in Arthur 1981 (pp.9–10) is
admissible relative to `M_0`; the Markdown of `ArthurTruncationStatement` ("The compact subgroup")
explains why admissibility cannot be stated with the Library's present objects. The identities of
Lemma 8.2 and (8.1) are exact, and no argument transferring them to every compact `K` with
`P_0(𝔸)K = G(𝔸)` is given here. As for Proposition 13.1(a),(b) in that module, each result is
therefore a predicate of one `K`, and `ArthurSiegelSetsStatement` asserts that one `K` satisfies
all of them at once. A single `K` is used because the results are applied together: Arthur's
proof of Proposition 13.2 (p.71) multiplies each summand of `Λ^T φ` by the left side of (8.1),
and his proof of Theorem 6.1 (p.41) substitutes (8.1) into the truncated kernel `k^T(x)`, which
is defined with the height of the same `K`.

An admissible `K` is a witness:

- it satisfies `hK`, is maximal compact and satisfies `IsPositiveTorusCompatible` for every
  actual Siegel setup, as explained in the Markdown of `ArthurTruncationStatement`;
- it admits Siegel covering data: Theorem 8.1 (Borel, Harish-Chandra) gives `T_1`, `ω` with
  `G(𝔸) = G(F) S^G(T_1, ω)`, and Arthur 1978 (p.941) fixes `ω`, `T_0` with
  `G(𝔸) = P_1(ℚ) S^{P_1}(T_0, ω)` for every `P_1` "by the properties of Siegel sets";
- it satisfies `IsTruncationIdempotent` by Proposition 13.1(a),(b), and `IsSiegelPartition`,
  `IsTruncationRapidDecay` by Lemma 8.2 and Proposition 13.2(a);
- it satisfies `IsRelativeSiegelPartition` by Arthur 1978, Lemma 6.4, or by (8.1). Arthur
  derives (8.1) "by applying Lemma 8.2 to `M_P` instead of `G`"; this uses that `K ∩ M_P(𝔸)` is a
  maximal compact subgroup of `M_P(𝔸)` admissible relative to `M_0` (Arthur 1981, property (iii)).

The existential statement is weaker than Arthur's results for every admissible `K`.

## Predicates

### `IsSiegelCovering hG hi hK hρ C T₁`

For compact factor data `C` (`ω = Ω_N Ω_M` and the compact subgroup `C.compactSubgroup`; see the
Markdown of `ArthurSiegelSets`) and `T_1 ∈ 𝔞_0`: for every standard `P_1` (`Δ_0^{P_1} = S₁`),
`G(𝔸) = P_1(F) · S^{P_1}(T_1, ω)`, with `P_1(F)` the image `parabolicRationalImage` of the
rational points of `Standard.parabolicHom i ν S₁`. This is the condition by which Arthur 1978
(p.941) fixes `ω` and `T_0`. For `P_1 = G` (`S₁ = Δ_0`) it is the property of Arthur 2005,
Theorem 8.1, with which Arthur fixes `T_1` and `ω` ("From now on, `T_1` and `ω` are to be fixed
as in Theorem 8.1").

### `IsSiegelPartition hG hi D hK hρ` (Arthur 2005, Lemma 8.2)

For every compact factor data `C` with `C.compactSubgroup = K` and every `T_1 ∈ 𝔞_0` with
`G(𝔸) = G(F) · S^G(T_1, ω)` (Theorem 8.1, with `G(F)` the published `rationalSubgroup F G`; the
covering for `G` alone), there is `c` such that for every `T` with `β(T) > c` for all `β ∈ Δ_0`
and every `x ∈ G(𝔸)`:

- for each standard `P`, only finitely many `δ ∈ P(F)\G(F)` have
  `F^P(δx, T) τ_P(H_P(δx) − T) ≠ 0`, and
- `∑_{P ⊇ P_0} ∑_{δ ∈ P(F)\G(F)} F^P(δx, T) τ_P(H_P(δx) − T) = 1`.

Here `P` runs over the `S ⊆ Δ_0`; `F^P = siegelIndicator … S T₁ Tp`;
`τ_P(H_P(·) − T) = ArthurRelative.tau … S Δ_0 (H_0(·) − T)`, which depends only on the projection
of `H_0(·) − T` to `𝔞_P` (`ArthurRelative.tau_eq`). The inner sums run over the published
`ParabolicRationalCosets` and evaluate at the chosen representatives `Quotient.out δ`; the terms
do not depend on the representative, since `F^P` is left `P(F)`-invariant and
`H_P(γy) = H_P(y)` for `γ ∈ P(F)` (product formula).

**Unique contributing pair.** Each term is a product of two `{0, 1}`-valued functions. By the
finite-support conclusion each inner unconditional sum `∑'` is an ordinary finite sum (Lean's
`∑'` is `0` for a non-summable family, so the conclusion is needed), and the total `1` means that
exactly one pair `(P, δ)` gives a nonzero term. This is Arthur's statement as he restates it
geometrically (p.39): for every `P` the projection of
`G_P(T) = {x ∈ P(F)\G(𝔸) : F^P(x, T) = 1, τ_P(H_P(x) − T) = 1}` to `G(F)\G(𝔸)` is injective, and
`G(F)\G(𝔸)` is the disjoint union of the images.

**Source reading.** The display of Lemma 8.2 (p.38) prints `τ_P(H_P(δx))`, without `T`. The
predicate uses `τ_P(H_P(δx) − T)`, as in the geometric restatement on p.39 and in Arthur 1978,
Lemma 6.4 (for `P = G`), to which Arthur refers for the proof ("See [A3, Lemma 6.4]", p.39; [A3]
is Arthur 1978).

Arthur 2005 asks for `T` "suitably regular" in the sense of the truncation parameter (`β(T)`
large for each `β ∈ Δ_0`); Arthur 1978 takes `T ∈ T_0 + 𝔞_0^+` suitably regular. Since `c` may
depend on `T_1`, a bound `c ≥ max_β β(T_1)` covers the second condition.

### `IsRelativeSiegelPartition hG hi D hK hρ` (Arthur 1978, Lemma 6.4; Arthur 2005, (8.1))

For every `C` with `C.compactSubgroup = K` and every `T_1` with `IsSiegelCovering hG hi hK hρ C T₁`
there is `c` such that for every `T` with `β(T) > c` for all `β ∈ Δ_0`, every standard `P`
(`Δ_0^P = SP`) and every `x ∈ G(𝔸)`:

- for each `P_1` with `P_0 ⊆ P_1 ⊆ P` (`S₁ ⊆ SP`), only finitely many `δ ∈ P_1(F)\P(F)` give a
  nonzero term, and
- `∑_{P_0 ⊆ P_1 ⊆ P} ∑_{δ ∈ P_1(F)\P(F)} F^{P_1}(δx, T) τ_{P_1}^P(H_{P_1}(δx) − T) = 1`,

with `τ_{P_1}^P = ArthurRelative.tau … S₁ SP` evaluated at `H_0(δx) − T` (it depends only on the
projection to `𝔞_{P_1}^P`) and the cosets `RelativeCosets S₁ SP` of
`Langlands.Global.ArthurTruncation`, evaluated at representatives in `P(F)`. As for
`IsSiegelPartition`, the finite supports and the `{0, 1}`-valued terms make the identity say that
exactly one pair `(P_1, δ)` contributes; this is how Arthur's proof of Lemma 6.4 concludes (p.942:
the sum is "at least one" and "at most one", by identifying the parabolic and the coset of any two
contributing terms). For `P = G` the identity is Lemma 8.2, under the stronger covering
hypothesis.

**Source reading.** The quotient is `P_1(F)\P(F)`, as in (8.1) (p.40) and in Arthur's use of
Lemma 6.4 in Arthur 1978, §7; the display of Lemma 6.4 (p.941) prints `P_1(ℚ)\G(ℚ)` in the
inner sum.

### `IsTruncationRapidDecay hG hi D hK hρ` (Arthur 2005, Proposition 13.2(a))

For a matrix representation `rho : G → GL_N` that is a closed embedding (`0 < N`,
`IsClosedSubgroup rho`), defining the height `‖x‖ = adelicSourceNorm F G rho x`, and a smooth
structure `hsmooth : SmoothOfRelativeDimension d G.X.hom` (the published enveloping-algebra
action uses its atlas), there is `c` such that for every `T` with `β(T) > c` for all `β ∈ Δ_0`
the following holds. If `f` is a published finite plot-smooth rational function
(`FinitePlotSmoothRationalFunctions F G`: continuous, left `G(F)`-invariant, smooth at the
infinite places, right invariant under an open compact subgroup of `G(𝔸_fin)`) with uniformly
moderate growth (`HasAdelicUniformModerateGrowth`: one exponent `r` with
`|(Xf)(g)| ≤ c_X ‖g‖^r` for every enveloping element `X` and every `g ∈ G(𝔸)`), then
`Λ^T f` is rapidly decreasing (`IsRapidlyDecreasing`): for every Siegel set `S^G(T_1, ω)` of `K`
and every `n`, `|Λ^T f(x)| ≤ B ‖x‖^{−n}` on `S^G(T_1, ω) ∩ G(𝔸)^1`.

**Relation to Arthur's statement.** Arthur's (a) concerns `φ ∈ C^∞(G(ℚ)\G(𝔸)^1)` uniformly
tempered: one `N_0` with `|(Xφ)(x)| ≤ c_X ‖x‖^{N_0}` for every left invariant differential
operator `X` on `G(ℝ)^1` and `x ∈ G(𝔸)^1`. The predicate is the case of the restrictions to
`G(𝔸)^1` of functions on `G(F)\G(𝔸)` with the published uniform growth on all of `G(𝔸)`:

- such a restriction is uniformly tempered, since the derivatives along `G(ℝ)^1` are among the
  enveloping derivatives (the enveloping action is by left invariant differential operators of
  the infinite group), and the bound holds on `G(𝔸)^1`;
- for `x ∈ G(𝔸)^1` the formula for `Λ^T f(x)` involves only the values of `f` at the points
  `nδx ∈ G(𝔸)^1`, so it is Arthur's `Λ^T` of the restriction;
- the source norm is polynomially equivalent to Arthur's height (see the Markdown of
  `ArthurSiegelSets`), so rapid decrease does not depend on the choice.

These three remarks are not formalized. Arthur imposes "suitably regular" on `T` throughout §13
(p.68: "For any suitably regular point `T ∈ 𝔞_0^+`"), and his proof uses (8.1). Here `c` may
depend on `rho` and `hsmooth` as well as on the group data and `K`.

Proposition 13.2(b), the estimate (13.5) ≤ (13.6) for measurable families of `C^r` functions, is
not stated.

## Statement

### `ArthurSiegelSetsStatement` (Lemma 8.2, (8.1), Propositions 13.1(a),(b) and 13.2(a))

For every number field `F`, connected reductive `G`, maximal split torus `i` and generic `ν`
there is a subgroup `K` with `hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` such that:

- `K` is maximal compact (`IsMaximalCompactSubgroup F G K`);
- `IsPositiveTorusCompatible F G T i ν T₀ j K` holds for every `T₀`, `j` with
  `IsSiegelAlgebraicSetup F G T i ν T₀ j`;
- for every `D` and every `hρ`:
  - there are compact factor data `C` with `C.compactSubgroup = K` and `T_1 ∈ 𝔞_0` with
    `IsSiegelCovering hG hi hK hρ C T₁`;
  - `IsTruncationIdempotent hG hi D hK hρ` (Proposition 13.1(a),(b));
  - `IsSiegelPartition hG hi D hK hρ`, `IsRelativeSiegelPartition hG hi D hK hρ` and
    `IsTruncationRapidDecay hG hi D hK hρ`.

The covering conjunct makes the two partition predicates non-vacuous for the chosen `K`: with
the data it provides they give Arthur's identities. The statement implies
`TruncationProjectionStatement` of `ArthurTruncationStatement` (keep the first two items and, for
each `D` and `hρ`, the conjunct `IsTruncationIdempotent`); a witness `K` of this statement is a
witness of that one.

## Qualifications

- `hρ` is an argument of every predicate, because the height of the definitions uses it (see the
  Qualifications of `ArthurTruncationStatement`).
- The compact subgroup is existential; see "The compact subgroup".
- The compact sets `ω` are the L1 products `Ω_N Ω_M` (see the Markdown of `ArthurSiegelSets`).
- The covering property is a hypothesis of the partition predicates and is asserted for the
  chosen `K` in `ArthurSiegelSetsStatement` (Theorem 8.1 and Arthur 1978, §6). The published L1
  reduction statement `AdelicSiegelFactors.AdelicSiegelReductionStatement` concerns the
  norm-one group and the torus of the derived group, and is not used.
- Proposition 13.2 is stated in the form (a) for functions on `G(F)\G(𝔸)` with uniform growth on
  `G(𝔸)`; (b) is not stated.

## Provenance

Source: Arthur 2005, Theorem 8.1, Lemma 8.2, (8.1) and Proposition 13.2(a), and the choice of
`K` on p.24; Arthur 1978, §6 and Lemma 6.4; Arthur 1981, §1. Derived formulations: the results
are stated as predicates of one compact subgroup together with the existence of a `K` satisfying
all of them; the formulation on `G(F)\G(𝔸)` over a number field, the Siegel sets built from the
L1 factor products, the finite-support form of the partition identities, the height from a closed
matrix representation and the class of functions with published uniform growth are explained
above.
