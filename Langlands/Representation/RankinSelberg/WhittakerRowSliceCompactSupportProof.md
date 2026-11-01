# Proof of compact support of Whittaker row data on a determinant slice

`Langlands.RankinSelberg.whittakerRowSliceCompactSupport` proves the unchanged
Library proposition
`Langlands.RankinSelberg.WhittakerRowSliceCompactSupportStatement.{uF,uV} F T n`
from `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement`.
Its exact type is

```text
{p : ℕ} → [Fact p.Prime] → (F : PadicField.{uF} p) → (T : F.TopologicalData) →
  (n : ℕ) → WhittakerRowSliceCompactSupportStatement.{uF,uV} F T n
```

It holds for every supplied topological data `T`, every `n` including `n = 0`
(that is, `GL₁`), and independent field and carrier universes `uF` and `uV`.
The statement pair and every pair it imports are used without modification.
The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

Worker 724 wrote the module and this note. The helper
`exists_iwasawa_diagonal_le_of_simpleRoot` reuses, nearly verbatim, the
Iwasawa and diagonal-bound part of Worker 887's published proof of
`Langlands.RankinSelberg.normalizedAbs_determinant_le_of_simpleRoot` in
`Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof`. That
published theorem concludes only a determinant bound and does not expose the
decomposition, so its argument is repeated here with a different conclusion.
Worker 887 is credited as coauthor for that reuse. The overall route is the one
sketched in the statement's Markdown and the proof task.

## What is proved

After installing `T.topology`, `T.valuativeRel` and `T.localField`, the proof
introduces every unitary additive character `ψ`, every carrier `V : Type uV`
with its `AddCommGroup` and `Module ℂ` instances, every representation `π` with
`hπ : IsSmooth π`, every `ℓ : glFunctionals ψ n π` (zero included), every
coefficient-image element `W : (coefficientModel π ℓ).toSubmodule` (zero
included), every `Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)` (zero included)
and every `k : ℤ`. It then proves exactly

```text
HasCompactSupport
  ((determinantSlice T n k).indicator
    (fun q : LeftUnipotentQuotient n F.Carrier =>
      whittakerNorm ψ W.val q * ‖Φ (quotientLastRow n q)‖))
```

on `LeftUnipotentQuotient n F.Carrier` with its quotient topology. The proof
adds no premise. It uses no measure, no irreducibility, admissibility, finite
type, multiplicity one, central character, gauge estimate or convergence fact.
The compact set constructed below depends on `W`, `Φ` and `k`; no uniformity is
claimed. Zero data need no separate case: the support is then empty and lies in
any set.

## Helper lemmas

The module adds three public lemmas in `Langlands.RankinSelberg`. Each takes
the topological data `T` as an explicit argument.

1. `exists_iwasawa_diagonal_le_of_simpleRoot`. Let `W : WhittakerFunctions ψ n`,
   `R > 0` and `C ≥ 0`. Assume that wherever `W (diag(a) κ) ≠ 0` with
   `κ` in the integral subgroup, every adjacent ratio satisfies
   `|a_i / a_(i+1)| ≤ R`. Let `W g ≠ 0` and let every entry of the last row of
   `g` satisfy `|x_j| ≤ C`. Then `g = u · (diag(a) · κ)` with `u` upper
   unipotent, `κ` in `Conductor.integralSubgroup` and
   `|a_i| ≤ R^(n-i) · C` for every `i : Fin (n + 1)`. Here `|·|` is
   `T.normalizedAbs`.

   The proof is the reused argument. `Iwasawa.exists_upperTriangular_mul`
   writes `g = b κ` with `b` upper triangular and `κ` integral. The diagonal
   entries of `b` are nonzero because `det b ≠ 0`. With `a_i = b_ii` and
   `D = Iwasawa.diagonalUnits a`, the matrix `u = b D⁻¹` is upper unipotent, and
   `g = u (D κ)`. Since `W (u x) = θ_ψ(u) W x`, also `W (D κ) ≠ 0`, so the
   hypothesis gives the ratio bounds at `(a, κ)`. The last rows of `g` and
   `D κ` agree (`lastRow_unipotent_mul`). The entry `(D κ κ⁻¹)_(n,n)` gives
   `a_n = Σ_j (D κ)_(n,j) (κ⁻¹)_(j,n)`. The entries of `κ⁻¹` are integral, so
   the ultrametric bound `normalizedAbs_finsetSum_le` gives `|a_n| ≤ C`.
   Reverse induction on `i` with `a_i = (a_i / a_(i+1)) · a_(i+1)` gives
   `|a_i| ≤ R^(n-i) · C`.

2. `normalizedAbs_det_of_mem_integralSubgroup`, reused from the shared
   `IntegralDeterminant` module. Every `κ` in the integral subgroup has
   `|det κ| = 1`: the determinants of `κ` and `κ⁻¹` are integral and their
   normalized absolute values multiply to one.

3. `isCompact_normalizedAbs_annulus_units`. For `0 < c`, the set of units
   `a : F.Carrierˣ` with `c ≤ |a| ≤ M` is compact in the topology of units.
   Pick `N` with `M < q^N`, where `q = T.residueCardinality > 1`
   (`pow_unbounded_of_one_lt`). The corresponding set `S` in the field is
   closed, since `T.normalizedAbs` is continuous. It excludes `0`, since
   `c > 0`. Comparing with `|ϖ^(-N)| = q^N` through
   `T.normalizedAbs_le_iff_of_ne_zero` and
   `LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs` and `_value` places `S`
   in the additive lattice `T.additiveLattice N`. That lattice is compact by
   `T.isCompact_additiveLattice`, hence so is `S`. The coercion
   `F.Carrierˣ → F.Carrier` is an embedding for a topological field
   (`Units.isEmbedding_val₀`). The annulus of units is the preimage of `S`,
   and `S` lies in the range of the coercion, so the preimage is compact
   (`IsInducing.isCompact_preimage'`).

## Main proof

1. *Hausdorff quotient.* The field is a topological additive group, so its
   right uniformity is a uniform additive group and the field is `T2`. The upper
   unipotent subgroup is closed (`GeneralLinear.UpperUnipotent.isClosed`), so
   `leftQuotient_t2Space` makes `LeftUnipotentQuotient n F.Carrier` Hausdorff.

2. *Constants.* `Whittaker.smoothSimpleRootSupport.{uF,uV} F T n ψ V π hπ ℓ W`
   gives `R > 0` bounding every adjacent Iwasawa ratio wherever `W.val` is
   nonzero, uniformly over the integral factor. This is the only use of
   `IsSmooth π`. `exists_schwartzBruhat_row_bound T n Φ` gives `C ≥ 0` with
   `|x_j| ≤ C` for every coordinate wherever `Φ x ≠ 0`. Put
   `M = max(R,1)^n · max(C,1) ≥ 1` and `c = q^(-k) / M^n > 0`.

3. *Compact set.* Let `A ⊆ (Fin (n + 1) → F.Carrierˣ)` be the product of the
   annuli `c ≤ |a_i| ≤ M`, compact by helper 3 and `isCompact_univ_pi`. Let
   `K` be the integral subgroup, compact as the level-zero open subgroup
   (`Conductor.levelSubgroup_zero`, `Conductor.isCompact_levelOpenSubgroup`).
   The map `Ψ(a, κ) = N · (diag(a) κ)` is continuous: it composes
   `GeneralLinear.continuous_diagonalUnits` with multiplication and with the
   continuous quotient map (`leftQuotient_isOpenQuotientMap`). Hence
   `Ψ '' (A ×ˢ K)` is compact.

4. *Support containment.* `HasCompactSupport.intro` reduces the goal to the
   following claim: the function vanishes outside `Ψ '' (A ×ˢ K)`. Take a
   coset `N g`, by `Quotient.inductionOn`, at which the indicator is nonzero.
   Then `N g` lies in the slice, which by
   `mk_mem_determinantSlice_iff_normalizedAbs` means `|det g| = q^(-k)`. Also
   `‖W(g)‖ · ‖Φ(η g)‖ ≠ 0` by `whittakerNorm_mk` and `quotientLastRow_mk`,
   so `W(g) ≠ 0` and `Φ(η g) ≠ 0`. The row bound then bounds the last row of
   `g`, and helper 1 gives `g = u · diag(a) · κ` with
   `|a_i| ≤ R^(n-i) C ≤ M`.

   The determinant of `g` equals that of `diag(a) κ`
   (`determinant_unipotent_mul`), which is `(∏ a_i) · det κ`. Helper 2 and
   multiplicativity of `T.normalizedAbs` give `∏_i |a_i| = q^(-k)`. For each
   `i`, the other `n` factors are at most `M`, so
   `q^(-k) ≤ |a_i| · M^n`, that is, `c ≤ |a_i|`. Thus `(a, κ) ∈ A ×ˢ K`.
   Finally `N g = N (diag(a) κ) = Ψ(a, κ)`, because
   `g (diag(a) κ)⁻¹ = u` lies in the upper unipotent subgroup
   (`QuotientGroup.rightRel_apply`).

`HasCompactSupport.intro` uses the Hausdorff property: a compact set in a `T2`
space is closed, so it contains the closure of the support. That closure is
then a closed subset of a compact set, hence compact.

For `n = 0` no separate argument is needed. The ratio bound is vacuous,
`M = max(C,1)` and `c = q^(-k)`. The single diagonal entry lies in the annulus
`q^(-k) ≤ |a_0| ≤ max(C,1)`.

## Source correspondence

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, source `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 406, 407 and 412 were read visually for this proof, and pages
385, 404–407 and 410–412 for the statement. No registered erratum concerns
these passages.

In §4.2, (4.2.1), p.406, the source sets `G_r^m = {g : |det g| = q^(-m)}`.
Here `r = n + 1` and the source index `m` is the integer `k`. On p.412, §4.6,
the source asserts: "It is easy to see (c.f. (4.2)) that the function
`W(g)Φ(η_r g)` on `G_r^m` is compactly supported modulo `N_r`." The argument
it points to is (4.2.3) on p.407. With `a = diag(a_1 ⋯ a_r, …, a_r)`, gauge
domination bounds the source coordinates `|a_i|` for `i < r`, which are
adjacent diagonal ratios. The condition `Φ_i(a_r) ≠ 0` bounds the last diagonal
entry. The Lean proof follows the same pattern of bounds. The published
uniform simple-root bound replaces gauge domination. The integral factor `κ`
of an Iwasawa decomposition, with a bound uniform in `κ`, replaces the source's
reduction through (2.7) to finitely many functions `W_i` on the torus. The
fixed determinant of the slice then gives the lower bounds,
which the source leaves implicit in "it is easy to see".

The proof establishes the source's form of the assertion. Every `g` in the
support has the form `u · (diag(a) κ)` with `u ∈ N_(n+1)` and
`(a, κ) ∈ A × K`. Hence the support lies in `N_(n+1) · C` for the compact set
`C = {diag(a) κ : (a, κ) ∈ A × K}`.

*Norm descent preserves the nonzero support.* The source function `W(g)Φ(η g)`
is not left `N`-invariant, since `W(u g) = θ_ψ(u) W(g)`. Its norm is invariant,
because `|θ_ψ(u)| = 1` and `η(u g) = η g`. The published `whittakerNorm_mk` and
`quotientLastRow_mk` give the descended value `‖W(g)‖ · ‖Φ(η g)‖` at `N g`.
This value is nonzero exactly when `W(g)Φ(η g) ≠ 0`. The support of the
descended function is therefore the image in `N \ G` of the source support.
On the slice the indicator does not change it, and off the slice it is zero.
Compactness of its closure in the Hausdorff quotient is the source's
"compactly supported modulo `N_r`" on `G_r^m`, and step 4 proves it through
exactly this nonvanishing criterion.

*Scope.* JPSS treat representations of Whittaker type (§2.1, p.385; §3.1,
p.404): admissible, of finite type, with a one-dimensional space of
`θ`-equivariant functionals. The Library statement quantifies all smooth
representations and all standard Whittaker functionals, including zero. This
is the project's derived extension of the source's setting, not a claim taken
from the source. Representations of Whittaker type are admissible, hence
smooth, so they are covered. The extension is proved because the only input
about `π` is `Langlands.Whittaker.smoothSimpleRootSupport`, which holds for
every actual coefficient of a smooth representation.

## Boundary

This module proves only the support assertion. It does not prove absolute
convergence of the inner `Ū_Q` integral of §4.6 or of (4.6.4). It proves no
quotient-measure tower identity and no equality of outer integrals. Compact
support alone is not used to infer any of these. The proof does not use
two-block factor multiplicativity, the Section 7 assembly, Section 9.3 or any
result depending on the dominant-rank analytic base. Its imports are the
statement module, `EqualRankSliceSupportProof` (for
`exists_schwartzBruhat_row_bound` and `normalizedAbs_finsetSum_le`),
`Analysis.Local.QuotientTopology`, `Group.GL.UpperBruhatCells`,
`Group.GL.NormalizedCharacter`, `HarmonicAnalysis.PadicLatticeTopology` and
`LocalField.Uniformizer`. The simple-root theorem is reached transitively
through `EqualRankSliceSupportProof`.
