# Lemmas II.1.4 and II.1.5 of Waldspurger on actual rational points

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable`,
namespace `Langlands.HarishChandraSchwartz`.

The module covers three things for the spherical function `Ξ = rationalXi` and the height
`σ = rationalHeight ρ` of the Library's `RationalWeights` on the actual rational points `G(F)` of a
connected reductive group:

- a proof of Lemma II.1.4, `Ξ(g⁻¹) = Ξ(g)`, with no structural hypothesis;
- the statement `RationalXiSquareIntegrableStatement` of Lemma II.1.5, which is conditional on
  two structural inputs from Renard Chapter V;
- the passage from the conclusion of Lemma II.1.5 to the Library's weight hypotheses
  `L2Weights` and `ConvolutionWeights`. Under these hypotheses the generic `L²` pairing and the
  convolution of Lemma III.6.1 apply to the actual Schwartz space `C(G) = RationalSchwartzSpace`.

The recorded declaration is the statement `RationalXiSquareIntegrableStatement`. It is a
proposition definition, not a proof.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers below are the
printed ones; the PDF page is the printed page minus 234. The author checked the quotations
against the text of PDF pages 6, 8, 18 and 38.

- I.1, printed p. 240: `K` is a special maximal compact subgroup, and `δ_H` "est le module du
  groupe `H`".
- I.1, printed p. 242: the norm comes from an algebraic embedding `τ : G → GL_n(F)`; "On peut
  supposer, et l'on suppose, que `τ(K) ⊂ GL_n(𝒪)`", and `σ(g) = log‖g‖`.
- Lemme II.1.4, printed p. 252: "Pour tout `g ∈ G`, `Ξ(g) = Ξ(g⁻¹)`. Cela résulte de l'égalité
  `π = π̌`."
- Lemme II.1.5, printed p. 252: "Il existe `d ∈ ℕ` tel que l'intégrale
  `∫_G Ξ(g)² (1 + σ(g))^{-d} dg` soit convergente." The proof reduces the integral, by I.1 (4)
  (Cartan decomposition), to the series `Σ_{m ∈ M̄₀⁺/M₀¹} mes(KmK) Ξ(m)² (1 + σ(m))^{-d}`. It then
  applies I.1 (5) (`mes(KmK) ≍ δ₀(m)^{-1}`), the upper bound of Lemme II.1.1 and I.1 (6)
  (`1 + σ(m) ≍ 1 + |H₀(m)|`), and finishes with the convergence of `Σ_{H ∈ H₀(M̄₀⁺)} (1 + |H|)^{-d}`
  over the lattice `H₀(M₀)`.
- Lemme III.6.1, printed p. 272: "Pour `f₁, f₂ ∈ C(G)`, l'intégrale ci-dessus est absolument
  convergente pour tout `g ∈ G`. La fonction `f₁ ∗ f₂` appartient à `C(G)`. L'application
  `C(G) × C(G) → C(G)`, `(f₁, f₂) ↦ f₁ ∗ f₂` est séparément continue en chacune des variables."
  Its proof uses Lemmes II.1.3, II.1.4 and II.1.5.

Renard, *Représentations des groupes réductifs p-adiques* (2026), V.5.1 and V.5.2, as itemized in
the Library's note `notes/renard/chapter-v-structural-inputs.md`. Row S19 covers V.5.1, which
includes the Cartan decomposition (4). Rows S20–S23 cover V.5.2, the simultaneous standard basis.

## Setting

`F` is a nonarchimedean local field of any characteristic. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, and
`hG : IsConnectedReductive G`. The torus map `i : S → G` is a maximal split torus (`hi`) and `ν`
is a generic cocharacter (`hν`). The minimal standard parabolic is
`P₀(F) = standardParabolicPoints i ν ∅`. `G(F) = rationalPoints G` carries the canonical topology
`rationalPointTopology F G.X` and its Borel σ-algebra; these are the local instances of
`RationalWeights`, together with second countability, the Hausdorff property and the
nonarchimedean group property (`Plancherel.rationalPoints_nonarchimedeanGroup`). `K` is a compact
open subgroup with `G(F) = P₀(F) K` (`hKo`, `hKc`, `hPK`). `ρ` is a matrix representation.

## Lemma II.1.4 (section `Inverse`, proved)

- `rationalPoints_modularCharacter_eq_one hG`: Mathlib's modular character of `G(F)` is
  identically `1`. This is the Library's proved `rationalReductiveUnimodularity`, applied with the
  proved `standardCocharacter`.
- `isClosed_standardParabolicPoints_empty hG hi hν`: `P₀(F)` is closed. This is the Library's
  `isClosed_standard_parabolic` for the empty set of simple roots, transported along
  `rootSet_empty`.
- `rationalMinimalModulus_eq_of_eq_empty`: a transport helper. An identity between the modular
  character of `P_J(F)` and the Haar modulus of conjugation on `U_J(F)` for an index set `J = ∅`
  is an identity for `δ₀ = rationalMinimalModulus`. The proof is by `subst`; the proof arguments
  of `HaarModulus.closedRestrictCharacter` agree by proof irrelevance.
- `rationalMinimalModulus_eq_modularCharacter hG hi hν`: for `p ∈ P₀(F)`,
  `δ₀(p) = Δ_{P₀(F)}(p)`, where `Δ_{P₀(F)}` is Mathlib's modular character of the locally compact
  group `P₀(F)`. The Library's `RationalParabolicModulusStatement` holds by
  `rationalParabolicModulus_of_reductiveUnimodularity`, applied to the proved
  `rationalReductiveUnimodularity` and `GroupScheme.dynamicCentralizerReductive`. The theorem is
  its case `I = ∅`, with the closedness of `U₀(F)` and `P₀(F)` and the continuity of the Levi
  projection (`continuous_standard_projection`) as its premises. So `δ₀`, which the Library
  defines as the radical modulus, is also the modular character of the group `P₀(F)` in Mathlib's
  convention, i.e. Waldspurger's `δ_{P₀}`, "le module du groupe `P₀`" (I.1, printed p. 240).
- **`rationalXi_inv hG hi hν hKo hKc hPK g`**: `Ξ(g⁻¹) = Ξ(g)`. This is the Library's generic
  `xi_inv` (module `SphericalInverse`), whose proof writes
  `Ξ(g) = ⟨ρ(g) e, e⟩` for the `G(F)`-invariant pairing `∫_K f₁ f₂` on `I_{P₀}^G 1` (invariant
  because `G(F)` is unimodular and `δ₀` is the modular character of `P₀(F)`) and uses the symmetry
  of that pairing. This is the source's argument `π = π̌`.

## Lemma II.1.5 (statement)

**`RationalXiSquareIntegrableStatement`**: for every universe-`u` nonarchimedean local field `F`,
every connected reductive `G`, maximal split torus `i`, generic cocharacter `ν`, and every
subgroup `K0` of `G(F)` such that

- `K0` is open and compact,
- `SimultaneousStandardBasisAt i ν K0` holds (Renard V.5.2: a normal compact open basis of `K0`
  with, for every standard parabolic `P_J`, a compatible split component and the Iwahori
  factorization and contraction clauses), and
- `Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0` holds (the covering clause of
  Renard V.5.1 (4): a finite set `F₀ ⊆ M₀(F)` with `G(F) = ⋃ K0 f a K0`, `f ∈ F₀`, `a` in the image
  of the dominant uniformizer chamber `C_A^+` of `S(F)`),

and for every compact open `K` with `G(F) = P₀(F) K`, every `N ≥ 1` and every closed matrix
representation `ρ : G → GL_N` (`IsClosedSubgroup ρ`), and every Haar measure `μ` on `G(F)`,

`SquareIntegrableWeight μ Ξ σ`, i.e. `∃ d : ℕ, ∫⁻ g, ofReal (Ξ(g)² (1 + σ(g))^{-d}) dμ(g) < ∞`,

where `Ξ = rationalXi hKc hPK` and `σ = rationalHeight ρ`.
`SquareIntegrableWeight` is the Library's form of the conclusion of II.1.5 (module
`SquareIntegrability`).

### Correspondence with the source

- The source fixes a special maximal compact `K` and an embedding with `τ(K) ⊂ GL_n(𝒪)`. The
  statement allows every compact open `K` with `G(F) = P₀(F) K` and every closed matrix
  representation `ρ`. The conclusion remains true in this generality: `Ξ` for such a `K` is a
  coefficient `⟨π(g)e_K, e_K⟩` of `I_{P₀}^G 1` (`rationalXi_eq_sphericalCoefficient`), and the
  argument of the source (Proposition I.4.3 for the pair `(e_K, e_K)`, then Lemma II.1.1) applies
  to it; changing `ρ` changes `1 + σ` only up to powers and constants. The proof is an
  obligation; the statement only asserts the conclusion.
- The quantifier over Haar measures is harmless: finiteness of the integral does not depend on
  the normalization.
- The two structural inputs are those used by the source's proof. The Cartan decomposition gives
  the reduction to a series. The basis gives the volume bound I.1 (5) and, through Proposition
  I.4.3, the upper bound of Lemma II.1.1. `K0` is assumed compact open. Without this the covering
  clause would be trivially satisfied by `K0 = G(F)`, and the cells `K0 f a K0` would not have
  finite measure.
- The remaining inputs of the proof are published as statements or proved:
  - the upper bound of Lemma II.1.1, `RationalXiUpperBoundStatement` (unproved; proof task Task
    5326);
  - upper Haar volume bounds for actual lattice cells, proved modulo the full center from the
    same basis property (`rationalLatticeQuotientVolume`, proving
    `RationalLatticeQuotientVolumeStatement`, Aubert project); its double-coset index estimates
    (`standardBasisMember_rayIndex`) are the input for the bound I.1 (5) in `G(F)` itself;
  - the one-sided I.1 (6) bound `RationalUniformizerCoordinateHeightStatement` (proved);
  - the lattice summation `summable_one_add_norm_rpow_neg` and the generic deduction
    `CartanSquareBound.squareIntegrableWeight` (proved, module `SquareIntegrability`).

## Weight adapters (section `Weights`, proved)

- `rationalL2Weights hKo hKc hPK ρ hsq`: from `hsq : SquareIntegrableWeight μ Ξ σ`, the Library's
  `L2Weights μ Ξ σ` (`Ξ > 0`, `σ ≥ 0` and the square-integrability clause). With it, the generic
  `L2Weights.integrable_conj_mul`, `memLp_two` and `eLpNorm_le` give the convergence of
  `(f₁, f₂)_G = ∫_G conj(f₁) f₂ dμ` (Waldspurger VII.1) on `C(G)`, and `C(G) ⊆ L²(G(F))`.
- **`rationalConvolutionWeights hKo hKc hPK ρ hG hi hν hKρ hsq`**: if moreover
  `hKρ : K ≤ rationalHeightSubgroup ρ` (that is, `ρ(K) ⊆ GL_N(𝒪)`, the source's
  `τ(K) ⊂ GL_n(𝒪)`), the Library's `ConvolutionWeights μ K Ξ σ`. Its fields are:
  - positivity and continuity of `Ξ` (`rationalXi_pos`, `continuous_rationalXi`);
  - nonnegativity and continuity of `σ`;
  - `1 + σ(g) ≤ (1 + σ(h))(1 + σ(h⁻¹ g))`, from subadditivity `rationalHeight_mul_le` via the
    generic `one_add_le_of_le_add`;
  - left `K`-invariance of `Ξ` and `σ` (`rationalXi_mul_mul`, and `rationalHeight_mul_mul` with
    `hKρ`);
  - Lemma II.1.4 (`rationalXi_inv`);
  - Lemma II.1.3 (`integral_rationalXi_mul_mul`);
  - `hsq`.

  These are exactly the hypotheses of the Library's generic Lemma III.6.1 (module
  `Convolution`): `Space.convolution` and `Space.convolutionBilin` on `Space Ξ σ`, which is
  `RationalSchwartzSpace`, and the separate continuity `Space.continuous_convolution_left` and
  `Space.continuous_convolution_right`.
- `RationalXiSquareIntegrableStatement.l2Weights` and
  `RationalXiSquareIntegrableStatement.convolutionWeights`: the same conclusions obtained from the
  statement and its hypotheses, for every Haar measure.

## Scope

- Lemma II.1.5 is not proved here. Its proof needs the inputs listed above, some of which are
  unproved statements.
- Lemma II.1.2 and Lemma II.1.6 on actual points are not treated.
- The existence of a special `K` with `G(F) = P₀(F) K` and of `K0` with the two structural
  properties is not proved here. In the Library they are among the conjuncts of the unproved
  `JointSpecialCompactBasisExistenceStatement` and `IwasawaExistenceStatement`.
- Provenance: the statement is a direct translation of Lemma II.1.5 with the structural premises
  displayed. `rationalXi_inv` is Lemma II.1.4 proved through the Library's generic
  `SphericalInverse`. The adapters are internal glue between `RationalWeights` and the generic
  modules `L2`, `Convolution` and `SquareIntegrability`.
