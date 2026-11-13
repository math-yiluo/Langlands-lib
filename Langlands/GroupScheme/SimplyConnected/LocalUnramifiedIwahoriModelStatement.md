# The Iwahori model of a Galois-stable chamber of a simply connected group

This module states `LocalSimplyConnectedUnramifiedIwahoriModelStatement`: a chamber of the
building over the maximal unramified extension that is stable under the Galois action has a
smooth model over `𝒪[F]` with connected special fibre whose points over the unramified
integers are exactly the stabilizer of the chamber. Nothing in this module is proved.

## Statement

Let `F` be a nonarchimedean local field (at universe `u`), `L = inertiaFixedField F` its
maximal unramified extension inside the separable closure, `Γ = Aut(L/F)` and
`G_L = baseChanged F L G`. The proposition quantifies over

- an affine `F`-group scheme `G` (`IsAffineHom G.X.hom`) with `IsSimplyConnected G`;
- arbitrary building data `C : MaximalUnramified.BuildingData F G_L` and arbitrary
  semilinear Galois data `D : MaximalUnramified.SemilinearApartmentData C`, whose action
  `D.action σ` on `C.ReducedBuilding` satisfies `D.action σ (g • y) = σ(g) • D.action σ y`
  (`action_smul`, with `σ(g) = rationalConjugate F L G σ g`);
- a chamber `Y₀` of `C` (`C.IsChamber Y₀`) with `D.action σ '' Y₀ = Y₀` for every `σ ∈ Γ`.

It asserts that there is an integral model `M : IntegralModel 𝒪[F] F G` such that

1. `M` is smooth over `𝒪[F]` (`M.IsSmooth`);
2. the special fibre of `M.group`, its base change along `Spec 𝓀[F] → Spec 𝒪[F]`, has a
   connected underlying space;
3. for every `g ∈ G(L)`, `g ∈ M.baseChangeUnramified.integralPoints` if and only if
   `(g • ·) '' Y₀ = Y₀`. Here `M.baseChangeUnramified` is the base change of `M` to the
   valuation ring `fixedFieldIntegers F` of `L`, and `integralPoints` is the image of its
   integral points in `G(L)`.

These are clauses 1, 2 and 5 of `LocalSimplyConnectedUnramifiedChamberStatement` for a given
`Γ`-stable chamber.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), with `k = F`, `K = L`,
`O` the valuation ring of `K` and `o` that of `k`, read with the authors' corrections of
1 November 2024:

- Theorem 8.3.13 (printed p. 299, PDF p. 330): the relative identity component `G_Ω^0` of the
  smooth model `G_Ω^1` has `G_Ω^0(O) = G(K)_Ω^0`; it is a smooth affine `O`-model of `G_K`
  with connected fibres (its proof is corrected on p. 37 of the corrections).
- 9.2.5 (printed pp. 327–328, PDF pp. 358–359): for a `Γ`-stable non-empty bounded `Ω`, the
  `O`-group schemes `G_Ω^1` and `G_Ω^0` descend uniquely (Fact 2.10.16) to smooth affine
  `o`-group schemes with generic fibre `G`; the special fibre of the descent of `G_Ω^0` is the
  identity component of that of `G_Ω^1`.
- 9.2.6 (printed p. 329, PDF p. 360): for a `Γ`-chamber `C`, `G_C^0(o)` is an Iwahori subgroup,
  and `G_C^0(O)` is the corresponding `Γ`-stable Iwahori subgroup of `G(K)`.
- 4.1.12(1) and Remark 4.1.13 (printed p. 161, PDF p. 192): `G(K)_C^0` is the stabilizer and
  the pointwise stabilizer of `C` in `G(K)^0`, and the stabilizer of a facet in `G(K)^♮` fixes
  it pointwise; 9.3.26 (printed p. 344, PDF p. 375): for semisimple simply connected `G`,
  `G(k)^0 = G(k)` and the stabilizer of a facet is its connected parahoric subgroup. Applied
  over `K` (where `G(K)^0 = G(K)` for simply connected `G`), the stabilizer of `C` in `G(K)` is
  `G_C^0(O)`.

The `Γ`-stability of the chamber makes its stabilizer `Γ`-stable: if `g • Y₀ = Y₀` then
`σ(g) • Y₀ = σ(g) • D.action σ Y₀ = D.action σ (g • Y₀) = Y₀`. This is the hypothesis under
which 9.2.5 descends the model.

## Provenance

This is a derived statement, not a numbered result of the source. It collects the Iwahori-model
clauses used in the proofs of KP Theorems 10.6.1 and 10.6.4 for simply connected `G`, stated
for the Library's supplied building data and semilinear Galois data over `L` rather than for
the constructed building of `G_L`. It asserts only the existence of a model with the listed
properties, not that the model is the Bruhat–Tits group scheme `G_{Y₀}^0`.
