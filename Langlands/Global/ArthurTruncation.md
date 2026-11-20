# Arthur's truncation operator

Module `Langlands.Global.ArthurTruncation`, namespace `Langlands.Global.ArthurTruncation`.
Worker 128, Task 5536, item 3. The propositions about these objects are stated in
`Langlands.Global.ArthurTruncationStatement` (see its Markdown).

The module defines Arthur's truncation operator `Λ^T` and the relative operators `Λ^{T,P}` on
functions on the actual adelic points `G(𝔸)` of a connected reductive group `G` over a number
field `F`, together with the constant terms and the height that they use. It proves one small
lemma (`pair_toA0`).

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):
  - §4, pp.22–24: standard parabolic subgroups `P ⊇ P_0`, `G(𝔸) = P(𝔸)K`,
    `H_P(nmk) = H_{M_P}(m)`;
  - §13, p.68, (13.1): for `T ∈ 𝔞_0` and `φ` locally bounded and measurable on
    `G(ℚ)\G(𝔸)^1`,
    `Λ^T φ(x) = ∑_P (−1)^{dim(A_P/A_G)} ∑_{δ ∈ P(ℚ)\G(ℚ)} ∫_{N_P(ℚ)\N_P(𝔸)} φ(nδx) τ̂_P(H_P(δx) − T) dn`;
    "the inner sum may be taken over a finite set (that depends on x)";
  - §13, p.73: for `P_1 ⊇ P_0` and `φ ∈ B_loc(P_1(ℚ)\G(𝔸)^1)`,
    `Λ^{T,P_1} φ(x) = ∑_{P_0 ⊆ Q ⊆ P_1} (−1)^{dim(A_Q/A_{P_1})} ∑_{δ ∈ Q(ℚ)\P_1(ℚ)} ∫_{N_Q(ℚ)\N_Q(𝔸)} φ(nδx) τ̂_Q^{P_1}(H_Q(δx) − T) dn`.
- J. Arthur, *The trace formula in invariant form* (1981), registered as
  `arthur-1981-trace-formula-invariant-form`, §1, p.9: admissible maximal compact subgroups.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*
  (2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
  printed page + 9), §2, p.312: the same operators for a number field `F`, on left
  `G(F)`-invariant locally bounded measurable functions on `G(𝔸)`, written with `φ_P` and
  `γ ∈ P\G`.

**Lapid's sign.** Lapid prints the sign of `Λ^{T,P}` as `(−1)^{dim 𝔞_Q^G}`. With that sign
`Λ^{T,G} = Λ^T` holds, but for `P ≠ G` the operator differs from Arthur's by the global sign
`(−1)^{dim 𝔞_P^G}`, and Arthur's cancellation (Proposition 13.3) fails. This module uses Arthur's
sign `(−1)^{dim(A_Q/A_P)} = (−1)^{dim 𝔞_Q^P}`; for `P = G` the two agree. Worker 3657 (executor
of the parent program) agreed with this reading.

Arthur works over `ℚ` and on `G(ℚ)\G(𝔸)^1`. The definitions here are pointwise formulas on
`G(𝔸)` over a number field `F`, as in Lapid. On `G(𝔸)^1` they are Arthur's.

## Setting

- `F` a number field; `G` a group scheme over `Spec F` (`IsAffineHom`,
  `LocallyOfFiniteType`, `hG : IsConnectedReductive G` where needed); `i : T.toGrp ⟶ G` a maximal
  split torus (`hi`), Arthur's `A_0`; `ν` a cocharacter fixing `P_0` (generic in the
  statements); `D` integral reflection data. These are the data of
  `Langlands.GroupScheme.ArthurRelative`, whose functions `tau`, `tauHat` and `weight` are used.
- Standard parabolic subgroups are the published closed representatives
  `Standard.parabolicScheme i ν S` with unipotent representatives `Standard.unipotentScheme i ν S`
  (module `StandardRepresentability`), indexed by finite sets `S ⊆ Δ_0` (`simpleFinset ν hG hi`
  is `Δ_0`). The module installs scoped instances (affineness, closed immersions, finite type)
  for these schemes.
- `K` is a compact subgroup with `P_0(𝔸)K = G(𝔸)` (`hK : IsIwasawaCompact
  (Standard.parabolicHom i ν ∅) K`). The definitions need nothing more: the height is well
  defined because `H_0` vanishes on the compact group `P_0(𝔸) ∩ K`.

## Definitions

- `toA0 hT hρ : Hom(X(P_0), ℝ) → 𝔞_0 = V T`. Arthur's `𝔞_0 = Hom(X(M_0)_F, ℝ)` is identified with
  `V T` through `X(P_0) ⊗ ℝ ≅ X(M_0) ⊗ ℝ ≅ X(A_0) ⊗ ℝ` (Arthur 2005, (5.1)), that is, through the
  restriction map `ArthurParabolicSpaces.restrictToTorus F i ν ∅` of the comparison module
  `Langlands.Global.ArthurParabolicSpaces`. The definition takes the bijectivity of that map as
  the explicit argument `hρ` and inverts it; `pair_toA0` gives `⟨ρ(μ), toA0 H⟩ = H(μ)`. The
  bijectivity follows from the comparison statement
  (`ArthurParabolicSpaces.bijective_restrictToTorus_empty` applied to
  `ParabolicSpacesComparisonStatement`, whose proof is a separate task).
- `height hi hK hρ x = toA0 (hK.height x)`: `H_0(x) = H_{P_0}(x)` in `𝔞_0`, from the published
  Iwasawa height `IsIwasawaCompact.height`. For a standard `P`, Arthur's `H_P(x)` is the
  projection of `H_0(x)` to `𝔞_P` (`x = p_0 k` with `p_0 ∈ P_0(𝔸) ⊆ P(𝔸)`), and every function
  of `H_P(x) − T` used here depends only on its `𝔞_P^G`- or `𝔞_P^Q`-component. So `H_0` is used
  throughout.
- `constantTerm F i ν S φ x = ∫_{N_P(F)\N_P(𝔸)} φ(nx) dn`: an abbreviation for the published
  L1 constant term `AdelicGroupPoints.subgroupConstantTerm F (Standard.unipotentHom i ν S) φ x`
  along the closed unipotent representative, with the published mass-normalized quotient Haar
  measure `AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure` (the invariant probability
  measure when `N_P(F)\N_P(𝔸)` is compact, as it is for an actual unipotent radical, published
  `unipotentRationalQuotientCompact`). `φ` is evaluated at chosen representatives, which is well
  defined for `φ` left `N_P(F)`-invariant.
- `HasConstantTerm F i ν S φ x`: the integrand of `constantTerm` is integrable for that measure,
  that is, the constant term is a convergent integral.
- `RelativeCosets SQ SP`: `Q(F) \ P(F)`, the right cosets in `P(F)` (the published
  `parabolicRationalSubgroup`) of its intersection with `Q(F)`.
- `truncation hG hi D hK hρ T φ x` is Arthur's (13.1): the sum over `S ⊆ Δ_0` of
  `(−1)^{|Δ_0 ∖ S|}` times the unconditional sum over `δ ∈ P(F)\G(F)` (published
  `ParabolicRationalCosets`, chosen representatives) of
  `φ_P(δx) · τ̂_P(H_0(δx) − T)`, with `τ̂_P = ArthurRelative.tauHat … S Δ_0`. Here
  `dim(A_P/A_G) = |Δ_0 ∖ S|`.
- `relativeTruncation hG hi D hK hρ SP T φ x` is Arthur's `Λ^{T,P}` for `Δ_0^P = SP`: the sum over
  `SQ ⊆ SP` of `(−1)^{|SP ∖ SQ|}` times the sum over `δ ∈ Q(F)\P(F)` of
  `φ_Q(δx) τ̂_Q^P(H_0(δx) − T)`, `τ̂_Q^P = ArthurRelative.tauHat … SQ SP`.
- `IsLocallyBoundedInvariant Γ φ`: Arthur's `B_loc` (measurable, bounded on compact sets, left
  `Γ`-invariant), for `Γ = G(F)` (`rationalSubgroup F G`) or `Γ = P(F)`
  (`parabolicRationalImage p`, the image of `P(F)` in `G(𝔸)`).

Sums over cosets are Lean's unconditional sums `∑'`, which are `0` when not summable. For each
`x` only finitely many terms are nonzero (the finiteness statement of the statement module), so
they are finite sums.

## Scope and qualifications

- The standard representatives are used as the standard parabolic subgroups and their unipotent
  radicals. Their identification with actual parabolic subgroups is the published classification
  (`standardParabolicClassification`) and related structural results; the published
  `StandardRepresentability` Markdown records which properties are established.
- `hρ` is an explicit argument (see `toA0`); it is discharged by the comparison statement once
  that is proved.
- The definitions use any compact `K` with `P_0(𝔸)K = G(𝔸)`. Arthur fixes a maximal compact
  subgroup admissible relative to `M_0` (Arthur 2005, p.24; Arthur 1981, §1, p.9), a condition
  the Library cannot yet express. The statement module states the parts of Arthur's results that
  hold for every such `K`, and states Proposition 13.1(a),(b) for a chosen `K` (see its
  Markdown, "The compact subgroup").
- Not included here: Proposition 13.2 (uniformly tempered functions truncate to rapidly
  decreasing ones), which needs heights `‖x‖`, Siegel sets and invariant differential operators,
  and Lemma 8.2 (the partition lemma), which needs the functions `F^P(x, T)` of truncated Siegel
  sets. They are a separate unit of Task 5536.

## Provenance

The operators are Arthur's (source). The encoding through the standard representatives, the
height in `V T` through `toA0` with the hypothesis `hρ`, the normalized quotient measure, the
chosen coset representatives and the unconditional sums are derived formulations, explained
above.
