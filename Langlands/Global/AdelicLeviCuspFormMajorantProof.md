# Weighted majorants of cusp forms on standard Levi subgroups: proof

Module `Langlands.Global.AdelicLeviCuspFormMajorantProof` proves the proposition
`Langlands.Global.LeviCuspFormPairingMajorantStatement` of module
`Langlands.Global.AdelicLeviCuspFormMajorantStatement`:

`Langlands.Global.leviCuspFormPairingMajorant : LeviCuspFormPairingMajorantStatement.{u}`.

Take a standard parabolic family `𝓕` of `G`, a subgroup `K` of `G(𝔸)` as in the statement,
a closed matrix embedding `rho : G → GL_N`, a standard index `J`, a cusp form `ψ` on
`M_J(F) \ M_J(𝔸)`, a point `g ∈ G(𝔸)` and a real `R`. The proof gives a constant `c·C ≥ 0`.
It then picks, for every class `q` of the norm-one quotient `M_J(F) \ M_J(𝔸)¹`, a representative
`x` with

`‖ι(x) g‖^R · |ψ(x)| ≤ c·C`,

where `‖·‖` is `RepresentationGrowth.adelicSourceNorm F G rho` and `ι` is the Levi embedding
`𝓕.l J ≫ 𝓕.p J`. The quotient has finite volume, so the constant function `c·C` is
integrable, and `HasLeviPairingMajorant J ψ g rho R` follows.

The hypotheses on `K` enter only through one consequence. The infinite part of `K ∩ M_J(𝔸)`
is maximal compact in `M_J(F_∞)`, and this is the compact subgroup `𝓕.leviInfiniteCompact` in
the definition of `IsLeviCuspForm`. The maximality of `K` in `G(𝔸)` and the Iwasawa
decomposition `P₀(𝔸) K = G(𝔸)` are not used. The Siegel representatives below use a compact
subgroup of `M_J(𝔸)` built for that purpose, and finitely many right translates.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`. Chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`: I.2.12 (Corollary, p.35) gives
rapid decrease on a Siegel domain, and I.2.18 (p.39) applies it to cusp forms. The Lean proof
uses the Library's own decay theorem `StandardParabolicFamily.adelicRelativeCuspidalRapidDecay`
(module `Langlands.Global.AdelicRelativeCuspidalRapidDecay`). That theorem bounds a function
whose constant terms along the relevant maximal parabolics vanish, using finitely many
derivatives with a common growth exponent; its paired Markdown describes its proof.

## Declarations

### `exists_rationalRepresentatives_cuspForm_rapidDecay`

**Hypotheses.** `H` is a connected reductive group over a number field `F`. It is affine and
locally of finite type, with a smooth relative dimension `hsmooth`. `Kinf` is a maximal compact
subgroup of `H(F_∞)`, and `rho` is a closed matrix embedding of `H` of positive size `N`. The
function `ψ : H(𝔸) → ℂ` is automorphic on `H(F) \ H(𝔸)` for `Kinf` and `rho`
(`IsAutomorphicFunctionOn` with `Γ = rationalSubgroup F H`). Its constant term
`subgroupConstantTerm F (r ≫ p') ψ` vanishes for every proper parabolic `p' : P' → H` with
geometric unipotent radical `r`, which is the form of `IsLeviCuspidal`.

**Conclusion.** There is a set `S ⊆ H(𝔸)` such that every norm-one point has a left `H(F)`
translate in `S`. For every natural `m` there is a constant `C` with
`|ψ(y)| · ht(y)^m ≤ C` for all `y ∈ S`, where `ht` is
`RepresentationGrowth.adelicHeight F H rho`.

*Proof.*
- `siegelAlgebraicSetupExistence` gives a Siegel setup `T, i, ν, T₀, j` of `H`. Then
  `exists_compact_openSubgroup_finite_cover` gives a compact subgroup `K` and a finite set `W` of
  norm-one points with `P₀(𝔸) (K W) = H(𝔸)`. With these, `exists_rational_mul_mem_weakSiegelProduct_mul`
  gives compact factors `C` with compact subgroup `K` and a threshold `t`. Every norm-one point
  then has a rational left translate in `S = S₀ W`, where `S₀` is the weak Siegel product
  `Ω_N Ω_M A_{T₀}(t) K`.
- `StandardParabolicFamily.ofMaximalSplitTorus` builds the canonical standard parabolic family
  `𝓕_H` of `H` from `i` and `ν`. Its minimal standard parabolic is
  `Standard.parabolicHom i ν ∅`, the one used by the Siegel product.
- `rationalAutomorphicRealization` realizes `ψ` as an automorphic form in the finite plot-smooth
  carrier. `adelicAutomorphicUniformGrowth`, followed by `hasAdelicUniformModerateGrowth_iff`,
  gives one natural exponent `e` that bounds every enveloping derivative by a constant times
  `ht^e`. By `evaluate_adelicDirectionalWordEnveloping`, a word of real right-orbit derivatives
  acts as the corresponding enveloping element. So every derivative word of `ψ` is bounded by a
  constant times `ht^e`.
- The decay theorem `adelicRelativeCuspidalRapidDecay` is applied to `𝓕_H`, the restriction
  `j : T₀ → T`, the full standard index `P = 𝓕_H.top`, the empty set of auxiliary characters,
  the one-point family `ψ` and the size `1`. Its hypotheses are checked as follows.
  - The restricted simple roots span `X*(T₀) ⊗ ℚ`
    (`ratSpan_restrict_simpleRelativeRoots_eq_top`, with `relativeRootNegation` and
    `relativeCharacterRootComplement`). `T₀` is split by the Siegel setup.
  - `ψ` is continuous, and its infinite slices are smooth
    (`InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff`). It is invariant on the right
    under an open subgroup of `H(𝔸_f)`.
  - `ψ` is invariant on the left under the rational points of `P₀`
    (`rationalImage_le_rationalSubgroup`). It is also invariant under the adelic points of the
    unipotent radical of the full standard parabolic, because their image lies in
    `parabolicQuotientSubgroup` at the full index, which is `H(F)`
    (`StandardParabolicFamily.parabolicQuotientSubgroup_top`).
  - `ψ` is cuspidal along `𝓕_H.top`. For `Q < top`, the parabolic `𝓕_H.p Q` is proper,
    because `𝓕_H.le_iff_range_le` would otherwise give `top ≤ Q`. The cuspidality hypothesis
    then kills `constantTerm Q ψ`.
  - The compact left factors form `Ω = Ω_N Ω_M`, the compact prefix. It lies in the image of
    `P₀(𝔸)`, since `Standard.unipotentHom` and `Standard.leviHom` factor through
    `Standard.parabolicHom`. The compact right factors form `K W`. The finite components lie in
    the compact set `fin(Ω) · fin(K W)`, because the positive torus factor has trivial finite
    component (`finite_positiveMap`).
  - With `P` the full index, the bounded-coordinate conditions are vacuous: no simple root lies
    outside `P`, and there are no auxiliary characters.
- A point of `S` is `y = n m a k w = p · a · (k w)`, with `p = n m ∈ Ω`, `a` in the weak chamber
  and `k w ∈ K W`. The decay theorem bounds `|ψ(y)| · ht(y)^m`.

### `adelicHeight_map_eq_adelicHeight_comp`

For `j : H → G` and a matrix representation `rho` of `G`,
`ht_rho(j(x)) = ht_{j ≫ rho}(x)` for every `x ∈ H(𝔸)`. Both sides evaluate the same matrix,
because adelic points map by postcomposition.

### `exists_closed_weight_bound`

**Hypotheses.** `j : H → G`, a matrix representation `rho` of `G` of size `N`, and a closed
matrix representation `rhoH` of `H` of the same size with `ht_rho(j(x)) = ht_{rhoH}(x)`;
`g ∈ G(𝔸)` and `R ∈ ℝ`.

**Conclusion.** There are a closed matrix embedding `rho'` of `H` of positive size and constants
`c ≥ 0` and `e ∈ ℕ` such that `‖j(x) g‖^R ≤ c · ht_{rho'}(x)^e` for all `x ∈ H(𝔸)`, where
`‖·‖ = adelicSourceNorm F G rho`. Every function automorphic for `rhoH` is automorphic for
`rho'`.

*Proof.*
- `N = 0`. `GL_0(𝔸)` has one element, so the source norm is the constant `‖1‖`. Take `c = ‖1‖^R`
  and `e = 0`. For `rho'` take the positive-size embedding of
  `exists_positiveMatrixEmbedding_of_isClosedSubgroup`, which keeps automorphy.
- `N > 0` and `R ≥ 0`. Take `rho' = rhoH`. The source norm is at most the height, the height
  is submultiplicative (`adelicHeight_mul_le`), and `ht ≥ 1`. So
  `‖j(x) g‖^R ≤ ht(g)^R · ht_{rhoH}(x)^R ≤ ht(g)^R · ht_{rhoH}(x)^{⌈R⌉}`.
- `N > 0` and `R < 0`. Take `rho' = rhoH`. Write `κ = N^{Σ_v m_v}`. Since `ht = κ · ‖·‖ ≥ 1`,
  the source norm is at least `κ⁻¹`. So `‖j(x) g‖^R ≤ (κ⁻¹)^R`, and `e = 0`.

### `leviCuspFormPairingMajorant`

*Proof.*
- The Levi `M_J` is connected reductive, by the field `isConnectedReductive` of
  `(𝓕.isCompatible J).levi`. The restricted embedding `𝓕.l J ≫ 𝓕.p J ≫ rho` is closed, since
  the Levi and parabolic inclusions are closed immersions.
- `exists_closed_weight_bound` gives `rho'`, `c` and `e` for `j = 𝓕.l J ≫ 𝓕.p J`.
- The subgroup `𝓕.leviInfiniteCompact (K.comap ofInfinite) J` equals the infinite factor of
  the maximal compact subgroup `K ∩ M_J(𝔸)` of `M_J(𝔸)` (`map_ofInfinite`). So it is maximal
  compact (`IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite`).
- `exists_rationalRepresentatives_cuspForm_rapidDecay`, applied with `rho'`, gives `S` and the
  bound `|ψ(y)| ht_{rho'}(y)^e ≤ C` on `S`.
- `isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive` makes
  `normOneRationalQuotientHaarMeasure F M_J` finite, so the constant `c·C` is integrable.
- For a class `q = [x₀]`, pick a rational `r` with `r x₀ ∈ S`. The point
  `x = rationalNormOne r · x₀` represents `q` (`LeftCosetSpace.mk_subgroup_mul`), and
  `‖ι(x) g‖^R |ψ(x)| ≤ c · ht_{rho'}(x)^e |ψ(x)| ≤ c·C`.
