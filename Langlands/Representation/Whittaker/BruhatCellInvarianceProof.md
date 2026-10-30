# Transpose invariance of bi-equivariant distributions on compatible Bruhat cells: proof

Authors: Worker 634, Worker 1011 and Worker 1087. Worker 634 wrote the complete private
proof `BruhatCellInvarianceCore.invariance_of_factorization` of the identical private
design statement, shared in parent draft revision 8 of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`
(`Langlands/Representation/Whittaker/BruhatCellInvarianceCore.lean`). Its zero-preserving
orbital lift (`exists_orbitalLift_preserving_zeros` below) adapts Worker 1011's
published surjectivity construction in
`Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof`, so Worker 1011 is a
coauthor. Worker 1087 ported the preparation into this module. The helpers moved to the
namespace `Langlands.Whittaker.BruhatCellInvariance`. `invariance_of_factorization` was
renamed `Langlands.Whittaker.bruhatCellInvariance_of_factorization` and now takes the
published `BruhatCellFactorizationStatement`. The final theorem applies it to the
published proof `bruhatCellFactorization`. The unused private cell-vanishing import was
removed. Worker 1087 also wrote the docstrings and this Markdown.

This module proves `Langlands.Whittaker.bruhatCellInvariance.{uF}`, whose type is exactly
the published proposition `Langlands.Whittaker.BruhatCellInvarianceStatement.{uF}` of
`Langlands.Representation.Whittaker.BruhatCellInvarianceStatement`. The statement module
and everything it imports are used unchanged. Besides the statement module, the proof
imports only the published modules

- `Langlands.Representation.Whittaker.BruhatCellFactorizationProof`, for
  `Langlands.Whittaker.bruhatCellFactorization` (the proof of
  `BruhatCellFactorizationStatement`) and, through its imports,
  `Langlands.Whittaker.bruhatOrbitalIntegration`, `cellSection`, `plusCoordinate` and
  their identities, `Langlands.GeneralLinear.upperBruhatCoordinates`,
  `Langlands.GeneralLinear.upperUnipotentFactorization` and
  `PadicField.canonicalGeneralLinearCompactOpen`;
- `Langlands.Representation.Whittaker.BruhatHaarMeasureProof`, for
  `Langlands.Whittaker.bruhatHaarMeasure` and `map_eq_self_of_antiInvolution`;
- `Langlands.Representation.Whittaker.CompatibleMonomialFixedProof`, for
  `Langlands.Whittaker.compatibleMonomialFixed`.

It adds no hypothesis, axiom or proof hole. The only axioms of the theorem are
`propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Everything the statement quantifies is kept: the universe `uF`, every prime `p`, every
p-adic field `F : PadicField.{uF} p` with its canonical normed field structure, every
`n : ℕ` (so every rank `n + 1`, rank one included), every unitary additive character `ψ`
and every permutation `w` of `Fin (n + 1)` with `(compatibleTorus ψ n w).Nonempty`. This
nonemptiness is the only premise on the cell. The conclusion is the statement's:

1. a proof `hτ` that `weylTransposeHomeomorph n F.Carrier` maps
   `upperBruhatCell (n + 1) F.Carrier w` into itself, and
2. for every algebraic distribution `D : Distribution (UpperBruhatCell (n + 1) F.Carrier w)`
   with `IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D`, the invariance
   `IsWeylTransposeInvariantBruhatCellDistribution n F.Carrier w hτ D`.

`D` is an arbitrary complex-linear functional on test functions. No continuity of `D`,
no cell stability, factorization, support, measure invariance, genericity or
countability is assumed. All Haar measures, the orbital integral, the cell coordinates,
the compact open subgroup and the factorization are constructed in the proof from
published theorems.

## Notation

Write `K` for the field, `U = upperUnipotent (n + 1) K`,
`P = U_w⁺ = permutationUnipotentPlus (n + 1) K w`, `H = Fin (n + 1) → Kˣ`,
`M = U × (H × U)`, `C = UpperBruhatCell (n + 1) K w`, `p_w = permutation (n + 1) K w`,
`h(d) = Iwasawa.diagonalUnits d`, `τ = weylTransposeHomeomorph n K` (the published
`g ↦ J gᵀ J`), `τ_U = weylTransposeUnipotent n K` (its restriction to `U`),
`π = upperBruhatTorusMap (n + 1) w : M → C`, `(u₁, d, u₂) ↦ u₁ p_w h(d) u₂`, and
`u • m = bruhatFiberAct (n + 1) K w u m`. The published fiber action sends
`(m₁, d, m₂)` to `(m₁ s u⁻¹ s⁻¹, d, u m₂)` with `s = p_w h(d)`.

## Declarations

All auxiliary declarations are in `Langlands.Whittaker.BruhatCellInvariance`.

### Section `Generic`

These work over any field `K` with a topology making it a topological ring, for
`w : Equiv.Perm (Fin (n + 1))` and `d : H`.

- `productTranspose n K : M ≃ₜ M` is the product exchange
  `σ (u₁, d, u₂) = (τ_U u₂, d, τ_U u₁)`. It swaps the two unipotent variables, applies
  `τ_U` to each and keeps the torus coordinate. It is its own inverse because `τ_U` is an
  involution.
- `transpose_inv`: `τ (g⁻¹) = (τ g)⁻¹`, because `τ` reverses products
  (`weylTransposeHomeomorph_mul`) and fixes `1`.
- `characterAverage_productTranspose ψ μ hμ α`: for a measure `μ` on `U` (Borel
  σ-algebra) that is s-finite, finite on compacts and satisfies
  `hμ : Measure.map τ_U μ = μ`,
  `characterAverage χ μ (pullback σ α) = characterAverage χ μ α` with
  `χ = standardCharacterContinuous ψ n`. At `d`, the left side is
  `∫ α (τ_U z₂, d, τ_U z₁) * ((χ z₁) * (χ z₂))⁻¹ d(μ × μ)(z)`. The map
  `E (z₁, z₂) = (τ_U z₂, τ_U z₁)` (the swap followed by `τ_U × τ_U`) preserves `μ × μ`,
  by `hμ` and Mathlib's `measurePreserving_swap`. Changing variables by `E` on the
  right side gives the integrand `α (τ_U z₂, d, τ_U z₁) * ((χ (τ_U z₂)) * (χ (τ_U z₁)))⁻¹`.
  The published `standardCharacter_weylTranspose` (`χ ∘ τ_U = χ`) and commutativity of the
  two complex factors make the two integrands equal at every `z`. The inverse-product
  weight of the published `characterAverage` is unchanged.
- `fiberTranspose_mem w d hs u` and `fiberTranspose w d hs`: let
  `hs : τ (p_w h(d)) = p_w h(d)` and `s = p_w h(d)`. For `u ∈ P`,
  `A(u) = s⁻¹ τ(u) s` lies in `P`. First, `s u s⁻¹ ∈ U` by the published
  `monomial_conj_mem_upperUnipotent`. Then `τ (s u s⁻¹) = s⁻¹ τ(u) s` (using
  `transpose_inv` and `hs`) lies in `U` by `weylTransposeHomeomorph_mem_upperUnipotent`.
  Second, `s A(u) s⁻¹ = τ(u) ∈ U`, and the published
  `permutation_conj_mem_upperUnipotent_of_monomial` gives `p_w A(u) p_w⁻¹ ∈ U`. The map
  `A`, with these values and continuity from that of `τ`, is a homeomorphism of `P` that
  is its own inverse: `A(A(u)) = s⁻¹ τ(s⁻¹ τ(u) s) s = u` by `hs`, `transpose_inv` and
  `weylTransposeHomeomorph_involutive`.
- `fiberTranspose_mul`: `A(u v) = A(v) A(u)`, since `τ` reverses products.
- `productTranspose_bruhatFiberAct w m hs u`: if `hs` holds for `d = m.2.1`, then
  `σ (u • m) = (A u)⁻¹ • σ m`. On the first coordinate both sides are
  `τ(m₂) τ(u)`. On the last coordinate, `τ (m₁ s u⁻¹ s⁻¹) = s⁻¹ τ(u)⁻¹ s τ(m₁) =
  (A u)⁻¹ τ(m₁)`, by `transpose_inv` and `hs`. The torus coordinates are both `d`.
- `fiberTranspose_measurePreserving w d hs ν`: let `P` carry a Borel structure and be
  locally compact and second countable, and let `ν` be a right-invariant Haar measure on
  `P`. Then `A` preserves `ν`, and so does `u ↦ (A u)⁻¹`. The published
  `map_eq_self_of_antiInvolution` applies to `A` (an involutive homeomorphism reversing
  products) and to inversion (also one, by `mul_inv_rev` and `inv_inv`), and the
  composite of measure-preserving maps preserves `ν`.
- `bruhatFiberAverage_productTranspose w ν α m hs`: with `K` Hausdorff, `P` locally
  compact and second countable, `ν` a right-invariant Haar measure on `P` (Borel
  σ-algebra) and `hs` for `d = m.2.1`,
  `bruhatFiberAverage ν (pullback σ α) m = bruhatFiberAverage ν α (σ m)`. Both sides are
  `∫ _ dν` by `bruhatFiberAverage_apply`. The left integrand is
  `α (σ (u • m)) = α ((A u)⁻¹ • σ m)` by `productTranspose_bruhatFiberAct`. Changing
  variables by the measure-preserving homeomorphism `u ↦ (A u)⁻¹` (Mathlib's
  `MeasurePreserving.integral_comp`) gives the right side. This is an equality of raw
  integrals of a single test function; no distribution is involved.
- `upperBruhatTorusMap_productTranspose w m hs`: with `hs` for `d = m.2.1`,
  `(π (σ m)).val = τ ((π m).val)`. Indeed
  `τ (m₁ s m₂) = τ(m₂) τ(s) τ(m₁) = τ(m₂) p_w h(d) τ(m₁)`.
- `transpose_mem_upperTriangular`: `τ` maps the upper triangular subgroup into itself,
  by the entry formula `(τ g) i j = g j.rev i.rev` (`weylTransposeHomeomorph_entry`).
- `cell_stable_of_fixed_monomial w d hs`: a single fixed monomial `p_w h(d)` gives
  `Set.MapsTo τ (upperBruhatCell (n + 1) K w) (upperBruhatCell (n + 1) K w)`. From
  `τ(h(d)) τ(p_w) = p_w h(d)` one gets `τ(p_w) = τ(h(d))⁻¹ p_w h(d)`. For
  `g = b₁ p_w b₂` with `b₁, b₂` upper triangular,
  `τ g = (τ(b₂) τ(h(d))⁻¹) p_w (h(d) τ(b₁))`. Both brackets are upper triangular by
  `transpose_mem_upperTriangular` and the published `diagonalUnits_mem_upperTriangular`.
  No stability of other cells is used or claimed.

### Section `Lift`

These work over a Hausdorff field `K` with a topology making it a topological ring, of
any rank `r`, for a permutation `w`. They take the coordinate homeomorphisms
`eT : U × H × U_w⁻ ≃ₜ C` with `(eT x).val = x₁ p_w h(x₂) x₃` and
`e : P × U_w⁻ ≃ₜ U` with `(e x).val = x₁ x₂`, the hypotheses `heT` and `he` stating
these laws. Write `cellSection eT` and `plusCoordinate e` for the published section and
plus coordinate of `BruhatOrbitalIntegrationProof`.

- `middleCoordinate_upperBruhatTorusMap heT he m`: `(eT⁻¹ (π m)).2.1 = m.2.1`. This is
  the torus component of the published identity
  `plusCoordinate e m • cellSection eT (π m) = m`
  (`bruhatFiberAct_plusCoordinate_cellSection`). The fiber action keeps the torus
  coordinate, and the torus coordinate of `cellSection eT c` is `(eT⁻¹ c).2.1`.
- `exists_orbitalLift_preserving_zeros heT he hK₀c hK₀o hK₀ ν I hI f`: let `K₀ ⊆ P` be
  compact, open and nonempty. Let `ν` be a Haar measure on `P` and `I` a complex-linear
  map with the evaluation formula `I α (π m) = bruhatFiberAverage ν α m`. Then every
  cell test function `f` has a preimage `α` with `I α = f` and `α m = 0` whenever
  `f (π m) = 0`. The construction is Worker 1011's: `φ` is the indicator of `K₀` with
  value `(ν.real K₀)⁻¹`, which is defined because `ν.real K₀ ≠ 0` (`K₀` is compact and
  nonempty open), and `α m = f (π m) * φ (plusCoordinate e m)`. `α` is locally
  constant because `f ∘ π` and `φ ∘ plusCoordinate e` are (`K₀` is clopen). Its support
  lies in the image of the compact set `tsupport f × K₀` under the continuous map
  `(c, u) ↦ u • cellSection eT c` (published `continuous_bruhatFiberAct_cellSection`),
  because every `m` equals `plusCoordinate e m • cellSection eT (π m)`. At a cell point
  `c`, `hI` at `m = cellSection eT c` gives
  `I α c = ∫ α (u • cellSection eT c) dν(u)`. Each integrand value is `f c * φ u`, by
  `upperBruhatTorusMap_bruhatFiberAct`, `upperBruhatTorusMap_cellSection` and
  `plusCoordinate_bruhatFiberAct_cellSection`. So `I α c = f c * ν.real K₀ * (ν.real K₀)⁻¹
  = f c` by `integral_const_mul` and `integral_indicator_const`. The vanishing clause is
  immediate from the product formula. This clause is what strengthens the published
  surjectivity.
- `supportedOn_middle_of_factorization heT he hK₀c hK₀o hK₀ χ μ ν I hI D τ S hτ hfac`:
  let `χ : U → ℂˣ` be continuous, `μ` an s-finite measure on `U` that is finite on
  compacts, and `ν`, `I`, `hI` as above. If `τ ∈ Distribution.supportedOn S` and
  `characterAverageDual χ μ τ = D.comp I`, then `D` is supported on the cell points
  `{c | (eT⁻¹ c).2.1 ∈ S}`. Let `f` vanish on that set, and take the lift `α` of `f`
  from the previous item. For `d ∈ S` and every `z`, `π (z₁, d, z₂)` has torus
  coordinate `d ∈ S` (`middleCoordinate_upperBruhatTorusMap`). So `f` vanishes there and
  `α (z₁, d, z₂) = 0`. Hence `characterAverage χ μ α` vanishes at every `d ∈ S`, being
  the integral of the zero function. By the support of `τ`,
  `τ (characterAverage χ μ α) = 0`. Finally
  `D f = D (I α) = characterAverageDual χ μ τ α = τ (characterAverage χ μ α) = 0`.
  `D` and `τ` are applied only to single test functions.

## The main proof

`bruhatCellInvariance_of_factorization hfac` proves `BruhatCellInvarianceStatement.{uF}`
from any proof `hfac` of the published `BruhatCellFactorizationStatement.{uF}`.
`bruhatCellInvariance` is `bruhatCellInvariance_of_factorization bruhatCellFactorization`,
with the published factorization theorem. The proof introduces `p`, `hp`, `F`, installs
`F.canonicalNormedField` and introduces `n`, `ψ`, `w` and the nonemptiness premise.

1. **Fixed monomials.** For every `d ∈ compatibleTorus ψ n w`, the published
   `compatibleMonomialFixed p hp F n ψ w d` gives `τ (p_w h(d)) = p_w h(d)`. Its
   hypothesis is the defining property of membership in `compatibleTorus`.
2. **Cell stability.** Take `d₀` from the premise. `hτ` is
   `cell_stable_of_fixed_monomial w d₀ _`. This is the first conclusion.
3. **Data.** For `D` and its bi-equivariance `hD`, the proof sets `U`, `P`, `H`, `M`, `C`
   with the Borel σ-algebras on `U` and `P`. `GeneralLinear (n + 1) F.Carrier` is
   locally compact and second countable by the published
   `F.canonicalTopologicalData.generalLinearLocallyCompactSpace` and
   `generalLinearSecondCountableTopology`. So `P` is locally compact (closed subgroup,
   published `isClosed_permutationUnipotentPlus`) and second countable (subspace).
   - The published `bruhatHaarMeasure p hp F n` gives a Haar measure `μ` on `U`. For
     it, the same theorem gives σ-finiteness (hence `SFinite`), right invariance and
     `Measure.map τ_U μ = μ` (`htranspose`). It also gives a Haar measure `ν` on `P`
     and its right invariance.
   - The published `bruhatOrbitalIntegration p hp F n w ν` gives a complex-linear
     `I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C` with the evaluation formula `hI` and
     surjectivity `hsurj`. Its support clause and uniqueness are not used.
   - `hfac p hp F n ψ w μ ν I hI D hD` gives `τ_H : Distribution H` with
     `τ_H ∈ Distribution.supportedOn (compatibleTorus ψ n w)` and
     `characterAverageDual χ μ τ_H = D.comp I`, `χ = standardCharacterContinuous ψ n`.
     Uniqueness is not used.
   - `upperBruhatCoordinates F.Carrier (n + 1) w` (second component) gives `eT` and
     its law. `upperUnipotentFactorization F.Carrier (n + 1) w` gives `e` and its law.
     `F.canonicalGeneralLinearCompactOpen (n + 1) Set.univ Filter.univ_mem` gives a
     compact open subgroup `L`, and `K₀ = Subtype.val ⁻¹' L ⊆ P` is compact (closed
     embedding), open and contains `1`.
4. **Support of `D`.** `supportedOn_middle_of_factorization` with `S =
   compatibleTorus ψ n w` gives `hDsupp`: `D` kills every cell test function that
   vanishes at all `c` with `(eT⁻¹ c).2.1 ∈ compatibleTorus ψ n w`.
5. **Reduction.** By the published `isWeylTransposeInvariantBruhatCellDistribution_iff`
   it suffices to show `D (pullback τ_C f) = D f` for every cell test function `f`,
   where `τ_C = bruhatCellWeylTranspose n F.Carrier w hτ`. By `hsurj`, `f = I α`.
6. **Exchange in the average.** `D (I (pullback σ α)) = D (I α)`. Both sides equal
   `τ_H (characterAverage χ μ _)` by the factorization. The two character averages
   are equal by `characterAverage_productTranspose ψ μ htranspose`.
7. **Exchange in the orbital integral, at compatible points.**
   `pullback τ_C (I α) - I (pullback σ α)` vanishes at every `c` with
   `(eT⁻¹ c).2.1 ∈ compatibleTorus ψ n w`. Let `m = cellSection eT c`, so `π m = c`
   and `m.2.1 = (eT⁻¹ c).2.1` is compatible. Hence `p_w h(m.2.1)` is fixed by `τ`
   (step 1), and `π (σ m) = τ_C c` (`upperBruhatTorusMap_productTranspose`). Then
   `I (pullback σ α) c = bruhatFiberAverage ν (pullback σ α) m
   = bruhatFiberAverage ν α (σ m) = I α (π (σ m)) = I α (τ_C c)`, by `hI`,
   `bruhatFiberAverage_productTranspose` and `hI` again.
8. **Conclusion.** By `hDsupp` and step 7, `D` kills that difference. Linearity of
   `D` (`map_sub`) and step 6 give
   `D (pullback τ_C (I α)) = D (I (pullback σ α)) = D (I α)`.

## Remarks on the route

- No algebraic distribution is commuted with an integral. The only integrals are the
  character average of one test function (step 6, via
  `characterAverage_productTranspose`) and fiber averages of one test function (step 7),
  compared by a change of variables in the measure. `D` and `τ_H` are only applied to
  single test functions, and only finite linearity (`map_sub`) is used.
- The Haar transport for `u ↦ (s⁻¹ τ(u) s)⁻¹` is proved, not assumed. It needs right
  invariance of `ν` (through `map_eq_self_of_antiInvolution`) and is used only at cell
  points over the compatible torus, where `s = p_w h(d)` is fixed by `τ`. Over the
  complement no comparison is made; the support of `D` from step 4 makes it unnecessary.
- The product exchange keeps the torus coordinate `d`. Shalika uses `w⁻¹θ(wh)` in the
  middle variable instead, which equals `h` on `H_χ`. Here the support of `τ_H` and of
  `D` is used directly, so no extension of a distribution from `H_χ` is needed.
- Rank one is not treated separately; the same argument covers `n = 0`.

## Provenance

The proof route is internal. It realizes, with the corrections noted above, the steps
outlined in the statement's Markdown (intended steps 1–5). These are motivated by the
proof of Proposition 1.8 in the nonempty-`H_χ` case on printed p.178 of J. A. Shalika,
*The multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193
(registered `shalika-1974-multiplicity-one`). They use properties (1.3)–(1.5) of θ on
printed p.174 in the forms `weylTransposeHomeomorph_mem_upperUnipotent`,
`standardCharacter_weylTranspose` and `compatibleMonomialFixed`. They are not verbatim
source statements. The statement's companion Markdown explains the derived scope and
conventions.

## Scope

This proves only `BruhatCellInvarianceStatement` (and the auxiliary
`bruhatCellInvariance_of_factorization`). It covers only cells with nonempty compatible
torus. It does not establish the empty-compatible-torus vanishing case, stability of
arbitrary cells, global transpose invariance of distributions on `GL_{n+1}` (Shalika's
Theorem 1.6), the finite-filtration assembly or Whittaker multiplicity one; those are
separate tasks.
