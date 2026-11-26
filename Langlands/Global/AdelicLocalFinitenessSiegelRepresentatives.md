# Rational representatives in a Siegel set with polynomially bounded height

Module `Langlands.Global.AdelicLocalFinitenessSiegelRepresentatives`. It proves that every point
of `G(𝔸)` has a rational left translate in a fixed Siegel-type region, with polynomial control of
its height. This is the input "rational representatives with polynomially bounded height" of the
weighted smoothing operator `AdelicWeightedSmoothingOperatorStatement`.

## Ambient logarithm and torus factors (namespace `AdelicGroupPoints`)

- `isIwasawaCompact_id`, `height_isIwasawaCompact_id`: the trivial subgroup is an Iwasawa subgroup
  for the identity `G → G`, whose height is the ambient logarithm `H_G = characterLog F G`.
  `characterLog_inv`: `H_G(g⁻¹) = −H_G(g)`.
- `exists_exp_abs_le_adelicHeight`: for connected reductive `G`, a closed matrix embedding `ρ` of
  positive size and a real linear form `φ` on the real character dual of `G`, there are `A > 0`,
  `r ≥ 0` with `exp |φ(H_G(g))| ≤ A ht_ρ(g)^r` for all `g`. Proof: the character lattice is free of
  finite rank (`rationalCharacters_free_finite_of_smooth`), so `φ` is the pairing with a real
  parameter `ν` (`realParameterPairing_surjective`); apply the polynomial bound of the finite
  maximum weight `max(⟨ν, ·⟩, ⟨−ν, ·⟩)` (`IsIwasawaCompact.iwasawaFiniteMaximumWeight`) for the
  Iwasawa subgroup of the identity.
- `exists_torusFactor`: let `T` be a split torus, `i : T → G`, and `L` a real linear section of
  the map of real duals `realCharacterDualMap i`. There are `A > 0`, `r ≥ 0` such that every `g` is
  `i(t) · g¹` with `t` in the positive torus `A_T`, `log t = L(H_G(g))`, `g¹` of norm one and
  `ht(i(t)) ≤ A ht(g)^r`. Proof: `t = positiveExp (L(H_G g))` (module `PositiveRealTorusLog`); then
  `H_G(i(t)) = H_G(g)`, so `i(t)⁻¹ g` has norm one. In coordinates `T ≅ G_m^I`, `t` has scalar
  coordinates `exp(ℓ(ε_k)/d)` with `ℓ = L(H_G g)`, `ε_k` the coordinate characters and `d = [F : ℚ]`;
  each `exp |ℓ(ε_k)|` is bounded by the previous item, and the height of `i(t)` is polynomial in
  the coordinate size (`exists_adelicHeight_map_full_le`).
- `exists_rootTrivialSection`: points `z_j` of `T` with `β(z_j) = 1` for every `β` in a set `Δ` of
  characters, whose ambient logarithms `H_G(i(z_j))` form a basis of the real dual of `G`, give
  such a section `L` with `L(l)(α) = 0` for `α ∈ Δ`: `L` sends the basis vector `H_G(i(z_j))` to
  `log z_j`.

## Siegel products (namespace `AdelicSiegelFactors`)

- `height_siegelProduct`: for an actual Siegel setup and an Iwasawa subgroup `K` of the standard
  minimal parabolic `P₀`, the height of `n m a k` (`n` in the standard unipotent group, `m` a
  norm-one point of the standard Levi, `a ∈ A_{T₀}`, `k ∈ K`) is the image of `log j(a)` under the
  map of real duals induced by `T → P₀`. The unipotent factor has zero logarithm
  (`characterLog_eq_zero_of_isUnipotent`), the norm-one Levi factor has zero logarithm, and the
  height is right `K`-invariant.
- `HasSiegelRepresentatives rho hK Ω M r θ`: every `x ∈ G(𝔸)` has a rational point `q` with the
  finite component of `q x` in `Ω`, `ht(q x) ≤ M ht(x)^r`, and `H₀(q x)` the image (under the map
  of real duals induced by `T → P₀`) of a torus functional `h` with `h(α) ≥ θ` for every simple
  root `α`.
- `exists_siegelRepresentatives`: assume an actual Siegel setup, compact factors `C` and a
  threshold `t₀` with the Siegel cover property `G(F) · S = G(𝔸)¹` for the weak Siegel product `S`
  (`IsSiegelCover`), `C.compactSubgroup` an Iwasawa subgroup, a section `L` as above with values
  vanishing on the simple roots, and centrality of the images of positive torus points whose
  logarithms vanish on the simple roots. Then there are a compact `Ω ⊆ G(𝔸_f)`, `M > 0` and
  `r ≥ 0` with `HasSiegelRepresentatives rho hK Ω M r (log t₀)`. Proof: write `x = z x¹` with `z = i(t)` from
  `exists_torusFactor`; `z` is central and `x¹` has norm one, so `x¹ = γ s` with `γ ∈ G(F)`,
  `s = n m a k ∈ S`, and `q = γ⁻¹` gives `q x = z s`. The finite component of `z` is trivial and
  those of `S` lie in a compact set (`exists_isCompact_finite_weakSiegelProduct`). The height bound
  combines `ht(z s) ≤ ht(z) ht(s)`, the norm minimality `ht(s) ≤ c ht(γ s)^e`
  (`siegelNormMinimalityStatement`) and `ht(γ s) = ht(z⁻¹ x) ≤ ht(z) ht(x)`. Finally
  `H₀(z s) = log t + log j(a)` transported to `P₀`, with `(log t)(α) = 0` and
  `(log j(a))(α) = log |α(j(a))| ≥ log t₀` on the weak simple-root chamber.

## Centrality (namespace `StandardParabolicFamily`)

- `commute_positiveSplitComponent_top`: the image of a point of the positive split component of the
  top index (`P = G`) commutes with every point of `G(𝔸)`: by
  `commutator_mem_radical_of_splitComponent` the commutator lies in the radical of `G`, which is
  trivial (`standardUnipotent_simple_eq_bot`), and the top standard parabolic is all of `G`.
- `commute_of_rootTrivial`: given `PositiveTorusSplitComponentStatement` (taken as a hypothesis), a
  positive point `t` of the maximal split torus with `(log t)(α) = 0` for all simple roots maps to a
  central point: its root values are `1` (a positive scalar idele of norm one is `1`), so `i(t)` is
  the image of a point of the positive split component of the top index.

## Provenance

The construction follows the Library proof `adelicRationalHeightReductionStatement_of_siegel`
(module `AdelicRationalHeightReduction`), with the central factor taken in the maximal split torus
so that its minimal-parabolic height has vanishing simple-root coordinates. Mathematical sources:
the factorization `G(𝔸) = A_G G(𝔸)¹` (Getz–Hahn, *An Introduction to Automorphic Representations*,
Lemma 2.6.2), Siegel sets and the polynomial almost-minimality of heights on them (Mœglin–
Waldspurger, *Spectral Decomposition and Eisenstein Series*, I.2.1–I.2.2 (vii), the latter in the
Library as `siegelNormMinimalityStatement`), used as in Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §7.4, proof of Lemma (2),
p. 216, where a Siegel domain containing the right translates of `S` by the support of the kernel
models the convolution operator (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`).
