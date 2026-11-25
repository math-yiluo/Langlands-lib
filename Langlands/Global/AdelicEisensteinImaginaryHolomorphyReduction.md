# Lapid's Proposition 6 from its premises

Module `Langlands.Global.AdelicEisensteinImaginaryHolomorphyReduction`
(namespace `Langlands.Global.ImaginaryAxis`) proves the published target
`Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` (Lapid 2011,
Proposition 6) from three premises:

- `Langlands.Global.EisensteinJointRootHyperplaneStatement.{0}` (module
  `AdelicEisensteinJointRootHyperplaneStatement`): near each `λ₀`, a product
  `Q` of powers of nonzero root forms turns the continued Eisenstein series
  into one function `h(s, g)`. This function is continuous on `W × G(𝔸)`,
  holomorphic in `s` and left `G(F)`-invariant.
- `Langlands.Global.BoundedWavePacketNormBoundStatement` (Lapid's Lemma 10,
  bound (19)).
- `Langlands.Global.IwasawaCompatibleMeasureExistenceStatement`: a Haar
  measure on `M(𝔸)` compatible with the Iwasawa decomposition.

The analytic tools are proved in the
modules `Langlands.Analysis.SeveralComplex.MeromorphicDomainExtension`
(gluing local holomorphic extensions), `ParametricIntegral` (holomorphy of
parametric integrals) and `RealHyperplaneDivision` (division by products of
real root forms). The module states the reduction as the proposition
`Langlands.Global.EisensteinImaginaryAxisHolomorphyReductionStatement`
(premises ⇒ target) and proves it as
`Langlands.Global.eisensteinImaginaryAxisHolomorphyReduction`.

## Declarations

- `inducedInnerProduct_const_mul`: `(a φ, a φ)_P = a ā (φ, φ)_P` for the
  published `inducedInnerProduct`. The scalar comes out of both integrals.
- `dense_setOf_prod_ne_zero`: for nonzero `ℂ`-linear forms `ℓ_β`, the set
  `{s | ∏ β, ℓ_β(s - s₀)^m ≠ 0}` is dense in `ℂⁿ`. A proper subspace has
  empty interior (`Submodule.eq_top_of_nonempty_interior'`). Finitely many
  dense open sets meet densely (Baire, `dense_biInter_of_isOpen`).
- `eisensteinImaginaryAxisHolomorphy_of_premises`: the target from the
  premises.
- `Langlands.Global.EisensteinImaginaryAxisHolomorphyReductionStatement`:
  the proposition `EisensteinJointRootHyperplaneStatement.{0} →
  BoundedWavePacketNormBoundStatement →
  IwasawaCompatibleMeasureExistenceStatement →
  EisensteinImaginaryAxisHolomorphyStatement`, and its proof
  `eisensteinImaginaryAxisHolomorphyReduction`.

## Proof

Let `E`, `D` be as in the target: `λ ↦ E λ g` is meromorphic with domain
`D` for every `g`, and `E = E(φ, ·)` on the `R`-regular parameters.

1. Coordinates. `ℂ ⊗ X^*(P)` is finite dimensional, hypothesis `hE`, so
   `ℝ ⊗ X^*(P)` is too. Fix `eR : ℝⁿ ≃ X^*(P) ⊗ ℝ` and its complex-linear
   extension `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` (module `ImaginaryAxisCoordinates`), with
   `e(i x) = imaginaryParameter (eR x)`.
2. Gluing. By
   `Langlands.Analysis.Meromorphic.exists_isMeromorphicInCoordinatesOn_extension`
   with `O = univ` and `Λ = i𝔞_P^*`, it suffices to find, for every
   `x₀ ∈ ℝⁿ`, one open `W' ∋ i x₀`. For every `g` we need a holomorphic `u`
   on `W'` with `u = E(e ·) g` on `W' ∩ e⁻¹ D`. The glued `E'` is meromorphic
   with a domain `D' ⊇ D ∪ i𝔞_P^*` and agrees with `E` on `D`.
3. Local data. Apply `EisensteinJointRootHyperplaneStatement` at
   `s₀ = i x₀`. It gives `S`, `m`, `W`, `h`. Put
   `ℓ_β = rootFunctional β ∘ e` and `Q(s) = ∏_{β ∈ S} ℓ_β(s - s₀)^m`, so
   `h(s, g) = Q(s) E(e s) g` on `W ∩ e⁻¹ D`. If `S = ∅` or `m = 0`, then
   `Q = 1` and `u = h(·, g)` works on `W`.
4. Away from the regular region. Otherwise choose `β₀ ∈ S`, a root of `A`
   in the unipotent radical. The real form
   `s ↦ B(Re(e s)|_A, β₀)` vanishes at `s₀`, since imaginary parameters have
   real part zero. So `W₁ = W ∩ {B(Re(e s)|_A, β₀) < 1}` is an open
   neighbourhood of `s₀`, and no `e s` with `s ∈ W₁` is `R'`-regular for
   `R' = max R 1` (`not_isRegularParameter_of_le`).
5. A continuation regular on the real slice. The given `D` need not contain
   any imaginary parameter. Apply the gluing theorem again with
   `O = e(W₁)` and `Λ = e(W₁ ∖ {Q = 0})`, using the local data `h / Q`. This
   gives `E₁`, meromorphic with a domain `D₁ ⊇ e(W₁ ∖ {Q = 0})`, with
   `E₁ = E` on `D` and outside `e(W₁)`. By step 4, `E₁ = E(φ, ·)` on the
   `R'`-regular parameters. A density argument gives
   `E₁(e s) g = h(s, g) / Q(s)` on `W₁ ∖ {Q = 0}`: both sides are
   continuous there, they agree on the dense open subset `e⁻¹ D`, and
   `Set.EqOn.of_subset_closure` applies.
6. Lemma 10. The Levi retraction `π` with `l ≫ π = 𝟙` is the Library's
   `IsRationalLeviSubgroup.exists_unipotentRadical_retraction`, applied to
   the Levi of the presentation. The instances `IsAffine U` and
   `IsClosedImmersion (iU ≫ p)` follow from `iU` being a closed subgroup of
   the affine `P`. `μ_M` comes from `IwasawaCompatibleMeasureExistenceStatement`,
   and `β` is a normalized bump function. For bounded measurable `c'`
   supported in a compact subset of `{x | i x ∈ W₁, Q(i x) ≠ 0}`, apply
   Lemma 10 with one inducing form `φ`, coefficient `c'` and continuation
   `E₁`. By `inducedInnerProduct_const_mul`,
   `Re(c'(x) φ, c'(x) φ)_P = |c'(x)|² Re(φ, φ)_P`. So the wave packets of
   `k(x, g) = E₁(i eR x) g` satisfy
   `∫ |Θ|² ≤ C ∫ |c'|² dλ` with `C = |Ω(P, P)| · Re(φ, φ)_P`.
7. Local division. `exists_local_division` (module
   `ImaginaryAxisLocalDivision`) applies with `ν` the Haar measure on
   `G(𝔸)`, `Γ = G(F)` and `c · vol = spectralMeasure n`, for a slice ball
   of radius `ρ` inside `W₁`, and with the division lemma
   `Langlands.Analysis.SeveralComplex.exists_open_forall_tendsto_eq_rootProduct_mul`
   for these `ℓ_β`.
   The `ℓ_β` are real on real points (`rootFunctional_complexify`) and
   nonzero, because `realRootFunctional β ≠ 0` by
   `EisensteinJointRootHyperplaneStatement`. It gives one `W' ∋ s₀` and,
   for every `g`, `H'` holomorphic on `W'` with `h(·, g) = Q · H'`.
8. Conclusion at `s₀`. On `W' ∩ e⁻¹ D ∩ {Q ≠ 0}`,
   `H' = h / Q = E(e ·) g`. Both `H'` and `E(e ·) g` are continuous on
   `W' ∩ e⁻¹ D`, and `{Q ≠ 0}` is dense (`dense_setOf_prod_ne_zero`), so they
   agree on `W' ∩ e⁻¹ D`. Thus `u = H'` is the local datum of step 2.

## Relation to Lapid's proof

Lapid (2011, §8, pp.329–330; registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`) argues by
contradiction at a generic point `λ₀` of a singular hyperplane `l = 0`,
where `E* = l^k E` is holomorphic and `E*(x₀, λ₀) ≠ 0`. He uses the
coefficient `φ(λ) = conj E(x₀, λ) φ₀` on `{|l| > η}`, the bound (19), and
continuity of `E*` in `x`. This proof uses the same three inputs: Lemma 10,
the root-hyperplane description, and continuity in `g`. It avoids the
generic point and the asymptotics in `η`. The coefficient is the conjugate
of an average of `E` over a small set `N ⊆ G(F) \ G(𝔸)`. Cauchy–Schwarz
then bounds the `L²` norm of `h / Q` on the real slice, for each `N`. The
division lemma for locally uniform limits passes to `N → {g₀}` and gives
holomorphy of `E(·)(g₀)` at `λ₀` for every `g₀`, with one neighbourhood for
all `g₀`.

## Scope

Only the target `EisensteinImaginaryAxisHolomorphyStatement` is proved,
from the premises above. The inner product formula of Lemma 10
(`BoundedWavePacketInnerProductStatement`) and the unitarity of `M(w, λ)`
are neither used nor proved; Lemma 10's bound (19) is used only through the
premise.
