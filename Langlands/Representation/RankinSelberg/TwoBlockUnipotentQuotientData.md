# The two-block unipotent quotient and its radical fiber average

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`,
namespace `Langlands.RankinSelberg.TwoBlockUnipotentQuotient`.

Author: Worker 778.

This module is a definitions unit for the first unfolding in JPSS (1983),
Section 4.6. It constructs the block-diagonal unipotent subgroup `H`, the
intermediate left quotient `H \ G`, the projection `H \ G → N \ G`, the radical
fiber map, the unweighted radical fiber integral, the radical average obtained
from it by quotient descent, and the determinant slices of `H \ G`. These are
internal infrastructure for that unfolding. They are not a numbered theorem of
the original.

## Source and conventions

Source: Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*
(1983), source ID `jpss-1983-rankin-selberg`, Section (4.6). The printed pages
410–412 are zero-based PDF indices 44–46. No errata note for this source exists
in the project literature.

- On printed page 411, equation (4) writes `Ψ^m(W, W'; Φ)` as an integral over
  `N \ G^m` of `Φ(ηg) W(g)` times the inner integral over the upper radical
  `x ↦ (1 x; 0 1)` of `f[(1 x; 0 1) g; e, e] θ((1 x; 0 1)) dx`.
- On printed page 412 the source rewrites this, formally, as the integral of
  `W(g) f[g; e, e] Φ(ηg)` over `N_(t_1,t_2) \ G_r^m`. Display (5) defines
  `N_(t_1,t_2)` as the group of matrices `diag(n_1, n_2)` with `n_i ∈ N_(t_i)`.
  Display (6), the disintegration through the first-block general linear
  group, is a later step that this module does not treat.

The correspondence with this module is as follows.

| JPSS | Here |
| --- | --- |
| block ranks `t_1`, `t_2` | `m 0 + 1`, `m 1 + 1` |
| total rank `r = t = t_1 + t_2` | `t + 1`, with `h : ∑ i, (m i + 1) = t + 1` |
| block shape | `B = succBlockShape m h` |
| `G_r` | `GeneralLinear (t + 1) F.Carrier` |
| `N_r` | `upperUnipotent (t + 1) F.Carrier` |
| `N_(t_1,t_2)`, display (5) | `blockUnipotent h F.Carrier` |
| `(1 x; 0 1)`, `x ∈ M(t_1 × t_2)` | `TwoBlockJacquet.upperRadical h F.Carrier x` |

Here `F : PadicField.{uF} p` is a canonical `p`-adic field for a prime `p`,
`t : ℕ` is arbitrary, and the two block ranks `m 0 + 1` and `m 1 + 1` are
positive. The source's `G_r^m = {g ∈ G_r : |det g| = q^(-m)}` (Section 4.2,
printed page 406) enters through determinant slices. `N \ G^m` is the
published slice `RankinSelberg.determinantSlice F.canonicalTopologicalData t m`
of `N \ G`, and `N_(t_1,t_2) \ G_r^m` is the slice `determinantSlice F h m` of
`H \ G` defined below. The fiber map and the averages are defined on all of
`GL_(t+1)`. The module has no representation or Whittaker hypotheses.

## The block-diagonal unipotent subgroup (sections `Algebra` and `Topology`)

The algebraic part holds over any commutative ring `R`.

- `BlockUnipotents m R` is the product `∀ i : Fin 2, upperUnipotent (m i + 1) R`
  of the two block upper-unipotent groups.
- `blockEmbedding h R` is the group homomorphism `(n_0, n_1) ↦ diag(n_0, n_1)`.
  It is the published Levi embedding `B.leviEmbedding R` composed with the
  inclusions of the two block unipotent groups. `blockEmbedding_apply`
  gives the representative formula
  `blockEmbedding h R n = B.leviEmbedding R (fun i => (n i).val)`. The lemmas
  `blockEmbedding_index_same`, `blockEmbedding_index_zero_one` and
  `blockEmbedding_index_one_zero` give its block entries.
  `blockEmbedding_injective` proves injectivity from the published
  injectivity of the Levi embedding.
- `blockUnipotent h R` is the subgroup `H`, defined as the actual image
  (`MonoidHom.range`) of `blockEmbedding h R`. `mem_blockUnipotent_iff`
  unfolds membership. `mem_blockUnipotent_iff_corner` gives an intrinsic
  description: `g ∈ H` exactly when `g` is upper unipotent and its upper-right
  `(m 0 + 1) × (m 1 + 1)` block vanishes. `H` is neither the upper radical
  nor the full upper-unipotent group.
- `mem_upperUnipotent_of_blocks` is a block criterion for upper unipotence:
  the lower-left block vanishes and both diagonal blocks are upper unipotent.
  It gives `blockEmbedding_mem_upperUnipotent`, the inclusion
  `blockUnipotent_le_upperUnipotent : H ≤ N`, and
  `upperRadical_mem_upperUnipotent`, which says that `(1 x; 0 1)` lies in `N`.
- Determinant one: `determinant_eq_one_of_mem_upperUnipotent` holds for upper
  unipotent matrices over any commutative ring. It gives
  `determinant_blockEmbedding` and `determinant_eq_one_of_mem_blockUnipotent`.
- `blockUnipotentEquiv h R : BlockUnipotents m R ≃* blockUnipotent h R` is the
  multiplicative equivalence. Its forward map is `blockEmbedding`
  (`blockUnipotentEquiv_apply_val`). Its inverse extracts the two diagonal
  blocks with the published `TwoBlockDeformation.unipotentLevi`
  (`blockUnipotentEquiv_symm_apply_val`). Entrywise, the `i`-th factor of
  `g ∈ H` has entries `g (B.index i a) (B.index i b)`
  (`blockUnipotentEquiv_symm_apply_apply`). `unipotentLevi_blockEmbedding`
  gives the left inverse law.
- `upperRadical_mul_upperUnipotent_mul` is the published factorization
  `upperRadical_mul_upperUnipotent` with a final right factor `g`:
  `u(x) (n g) = diag(n_0, n_1) (u(n_0⁻¹ (β + x n_1)) g)`, where the diagonal
  factor is `blockEmbedding` of the blocks `unipotentLevi h n`, so it lies in
  `H`. It is a rewrite of the published lemma, and its matrix proof is not
  repeated.

Topology (section `Topology`, for a topological ring `R`):
`continuous_blockEmbedding`, `continuous_unipotentLevi` (continuity of the
published diagonal-block extraction on `N`, from the published continuous Levi
projection), and `blockUnipotentHomeomorph`, the equivalence as a
`ContinuousMulEquiv`. For any Hausdorff topology on `R`, `isClosed_blockUnipotent`
proves that `H` is closed: it is the intersection of the closed group `N` with
the closed conditions that the upper-right block vanishes.

For the canonical `p`-adic topology (section `Canonical`), the module records
`canonicalBlockUnipotentHomeomorph`, `continuous_blockUnipotentEquiv`,
`continuous_blockUnipotentEquiv_symm` and `isClosed_blockUnipotent_canonical`.

## The intermediate quotient and the projection (section `Quotient`)

These constructions hold over any field `K`.

- `mk_mul_of_mem` is a small generic lemma: `[u g] = [g]` in
  `LeftQuotient P` when `u ∈ P`.
- `BlockQuotient h K` is the actual left quotient
  `QuotientIntegration.LeftQuotient (blockUnipotent h K) = H \ GL_(t+1)(K)`.
  It is the quotient by the relation `g ~ g'` iff `g' g⁻¹ ∈ H`, with the
  quotient topology.
- `projection h K : BlockQuotient h K → LeftUnipotentQuotient t K` is the
  canonical map `[g]_H ↦ [g]_N` from the finer quotient onto the coarser one.
  It is defined with `QuotientIntegration.descend` of `g ↦ [g]_N`. That map is
  left `H`-invariant because `H ≤ N`. The codomain is the published
  `LeftUnipotentQuotient t K`. The lemmas are `projection_mk` (representative
  formula) and `projection_surjective`.
- `fiberPoint h K x g = [u(x) g]_H` is the radical fiber map on
  representatives, with `u(x) = upperRadical h K x`. `fiberPoint_def` is the
  representative formula. `projection_fiberPoint` proves
  `projection (fiberPoint x g) = [g]_N`, because `u(x) ∈ N`.
- `fiberPoint_upperUnipotent_mul`: for `n ∈ N`,
  `fiberPoint x (n g) = fiberPoint (n_0⁻¹ (β + x n_1)) g`, the published
  `unipotentShift`. This follows from `upperRadical_mul_upperUnipotent_mul`,
  because the diagonal factor lies in `H`.

## Topology of the quotient (section `Padic`)

All topologies are the canonical `p`-adic ones
(`F.canonicalTopologicalData.topology`), with matrix, subtype, product and
quotient topologies induced from it.

- `t2Space_blockQuotient`: `H \ G` is Hausdorff, since `H` is closed.
- `continuous_projection`: the projection is continuous, because it is the lift
  of the continuous quotient map `g ↦ [g]_N`.
- `continuous_fiberPoint`: `(x, g) ↦ [u(x) g]_H` is jointly continuous, by the
  published continuity of `upperRadical` and of multiplication in `GL_(t+1)`.
- `projection_rightTranslate` and `fiberPoint_mul`: the projection and the fiber
  map are compatible with the published right translations
  `QuotientIntegration.rightTranslate`.

## The radical fiber integral and its descent (section `Average`)

Fix any measurable structure on `F.Carrier`. The rectangle
`Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier` carries Mathlib's product
measurable structure.

- `fiberIntegral F h μ f g = ∫ x, f (fiberPoint h F.Carrier x g) ∂μ` for a
  measure `μ` on the rectangle and a scalar function `f : H \ G → ℂ`. This is
  the ordinary total Bochner integral, so its value is `0` when the integrand
  is not integrable (`fiberIntegral_def`).
- `fiberIntegral_upperUnipotent_mul`: for a Borel structure on the canonical
  field, every additive Haar measure `μ` on the rectangle, every `f`, every
  `n ∈ N` and every `g`,
  `fiberIntegral μ f (n g) = fiberIntegral μ f g`. By
  `fiberPoint_upperUnipotent_mul` the left side is the integral of
  `y ↦ f (fiberPoint y g)` composed with `x ↦ n_0⁻¹ (β + x n_1)`. The
  published `TwoBlockDeformation.integral_comp_unipotentShift` says that this
  substitution preserves every Bochner integral against `μ`. No rectangular
  scaling or Haar argument is repeated here.

  No integrability hypothesis is needed. The substitution is an actual
  measurable equivalence that preserves `μ`, so it carries the integrand to
  an integrable function exactly when the integrand is integrable. Both
  integrals are therefore equal whether or not the integrand is integrable.
  This invariance gives no convergence: a non-integrable integrand has both
  sides equal to `0`.
- `fiberIntegral_mul`: right translation of the base point,
  `fiberIntegral μ f (g g') = fiberIntegral μ (f ∘ rightTranslate g') g`.
- `radicalAverage F h μ f : LeftUnipotentQuotient t F.Carrier → ℂ` is
  `QuotientIntegration.descend` of `fiberIntegral F h μ f`. The descent uses
  the left `N`-invariance above, so no coset representative is chosen.
  `radicalAverage_mk` gives the representative evaluation
  `radicalAverage μ f [g]_N = ∫ x, f [u(x) g]_H dμ(x)`.
  `radicalAverage_rightTranslate` gives
  `radicalAverage μ f (q · g) = radicalAverage μ (f ∘ rightTranslate g) q`.

The average has no character kernel. In the unfolding of (4), the factor
`θ((1 x; 0 1))` is absorbed by the standard character of `W`, since
`W(u(x) g) = θ(u(x)) W(g)`. On `H` the standard character of `W` cancels the
character from the inverse-character Jacquet coefficient `f[·; e, e]`, and
`Φ(η u(x) g) = Φ(ηg)`. The integrand of the source is then a left
`H`-invariant function evaluated at `u(x) g`, which is the shape
`f (fiberPoint x g)` used here. This paragraph only motivates the
construction; the module proves none of these facts about `W`, `f` or `Φ`.

## Determinant slices (section `Padic`)

These reuse the published normalized order `F.canonicalTopologicalData.ord`
and the published slices `RankinSelberg.determinantSlice` of `N \ G`. No
second valuation normalization is introduced.

- `determinantSlice F h k` is the preimage under `projection` of
  `RankinSelberg.determinantSlice F.canonicalTopologicalData t k`
  (`mem_determinantSlice`).
- `mk_mem_determinantSlice`: `[g]_H` lies in the slice `k` exactly when
  `ord(det g) = k`.
- `isClopen_determinantSlice` holds because the projection is continuous.
  `measurableSet_determinantSlice` holds for every Borel structure on `H \ G`.
- `determinantOrder_projection_fiberPoint` and
  `fiberPoint_mem_determinantSlice_iff`: the fiber point `[u(x) g]_H` has the
  same slice order as `[g]_N`.
- `pairwise_disjoint_determinantSlice` and `iUnion_determinantSlice`: the slices
  are pairwise disjoint and cover `H \ G`.

## What is not asserted

This module asserts none of the following:

- a quotient-measure tower identity relating integrals over `H \ G`,
  `N \ G` and the rectangle;
- existence, compatibility or normalization of quotient measures;
- integrability, convergence or a Fubini theorem;
- equality of the two outer integrals of the source;
- the disintegration (6) through the first-block general linear subgroup.

It contains no Whittaker-functional realization, induced representation,
functional equation or factor multiplicativity. Those are separate units.
