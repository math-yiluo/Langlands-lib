# The projections `p_χ` of Waldspurger VIII.4 on actual rational points

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralProjection`,
namespace `Langlands.HarishChandraSchwartz`.

The module brings the Library's generic projection `p_χ` (module `CentralProjection`, hypotheses
`CentralWeights`) to the actual rational points. It contains:

- proofs that the image `A_G(F)` of a central `s : T → G` lies in every actual standard Levi and
  parabolic subgroup, that `δ₀` is trivial on central elements of `P₀(F)`, and that
  `Ξ(a g) = Ξ(g)` for `a ∈ A_G(F)`;
- the statement `RationalSplitCenterHeightStatement` of two height properties of `A_G(F)` and
  `G¹`, which Waldspurger uses without comment in VIII.4;
- from these, the Library's `CentralWeights` for the actual weights, the projection
  `rationalCentralProjection` (`p_χ`) on the actual `C(G)`, and the rapid decay of `p_χ f` on
  `G¹`.

The recorded declaration is the statement `RationalSplitCenterHeightStatement`. It is a
proposition definition, not a proof.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers below are the
printed ones; the PDF page is the printed page minus 234. The author checked the quotations
against the text of PDF pages 5, 93 and 94.

- I.1, printed p. 239: `A_G` is the largest split torus in the center of `G`;
  `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`; "L'application de restriction `Im X(G) → Im X(A_G)` est
  surjective de noyau fini." I.1, printed p. 242: `σ(g) = log‖g‖` and (6)
  `1 + σ(m) ≍ 1 + |H₀(m)|` on `M₀`.
- VIII.4, printed p. 327: "Notons `Â_G` l'ensemble des caractères unitaires de `A_G` [...] On
  définit une application `p_χ : C(G) → C_lisse(G)_χ` par la formule
  `(p_χ f)(g) = ∫_{A_G} χ^{−1}(a) f(ag) da`. L'intégrale est absolument convergente."
- Proof of Proposition VIII.4.1, printed p. 328: "D'autre part, on vérifie aisément que pour
  tout `f ∈ p_χ(°C(G))` et tout `r ∈ ℝ`, il existe `c > 0` tel que, pour tout `g ∈ G¹`, on ait
  l'inégalité `|f(g)| ⩽ cΞ(g)(1 + σ(g))^{−r}`."

The source gives no argument for the two assertions. They rest on the behaviour of `σ` on the
split centre: `σ` on `A_G` is comparable to the norm of `H_G`, `H_G` is trivial on `G¹`, and
`A_G / (A_G ∩ G¹)` is a lattice. `RationalSplitCenterHeightStatement` isolates exactly what the
Library's generic `CentralProjection` needs for this.

## Setting

`F` is a nonarchimedean local field of any characteristic. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]`, and `[LocallyOfFiniteType G.X.hom]` from the section `Weights` on.
`G(F) = rationalPoints G` carries the canonical topology and its Borel σ-algebra (the local
instances of `RationalWeights`), with second countability, the Hausdorff property and the
nonarchimedean group property. `i : S → G` is a torus map and `ν` a cocharacter, defining
`P₀(F) = standardParabolicPoints i ν ∅`. `s : T → G` is a homomorphism from a commutative group
scheme. `IsCentral s` means that `s` factors through the scheme center of `G`; a split
component (`IsSplitComponent s`) is central. Its image `A_G(F) = (rationalPoints.map s).range`
carries the subspace σ-algebra. `K` is a compact open subgroup with `G(F) = P₀(F) K`,
`Ξ = rationalXi hKc hPK`, `σ = rationalHeight ρ` for a matrix representation `ρ`, and
`G¹ = Plancherel.rationalCommonNormKernel G`.

## Proved results (no structural input)

- `iwasawaWeight_mul_left_of_eq_one` and `xi_mul_left_of_eq_one` (abstract, for `G = P K`): if
  `z ∈ P` has `δ(z) = 1`, the Iwasawa weight satisfies `w(z g) = w(g)`. If moreover `z` commutes
  with `K`, then `Ξ(z g) = Ξ(g)`. These come from `iwasawaWeight_mul` (module `Spherical`).
- `range_le_standardLeviPoints i ν hs J` and `range_le_standardParabolicPoints i ν hs J`: for
  central `s`, `A_G(F) ⊆ M_J(F)` and `A_G(F) ⊆ P_J(F)` for every `J`. A point of `A_G(F)` lies in
  the scheme center, hence in the centralizer of the torus (`center_le_torusCentralizer`), hence
  in `M_J(F)` (`torusCentralizer_le_standardLevi`) and in `P_J(F)`.
- `rationalMinimalModulus_eq_one_of_mem_center i ν p hp`: `δ₀(p) = 1` for `p ∈ P₀(F)` central in
  `G(F)`. Conjugation by `p` is the identity of `U₀(F)`
  (`closedNormalizerCharacter_eq_one_of_commute`).
- `rationalXi_mul_of_mem_range hKo hKc hPK hs ha g`: `Ξ(a g) = Ξ(g)` for `a ∈ A_G(F)`.
- `one_add_rationalHeight_le_mul ρ a g`: `1 + σ(a) ≤ (1 + σ(a g)) (1 + σ(g))` for all
  `a, g ∈ G(F)`, from `σ(x y) ≤ σ(x) + σ(y)` and `σ(g⁻¹) = σ(g)`.
- `rationalCentralWeights hKo hKc hPK hs ρ muA hint`: the Library's
  `CentralWeights muA Ξ σ` for a measure `μ_A` on `A_G(F)`, given
  `hint : ∃ r₀, ∫⁻_{A_G(F)} (1 + σ(a))^{-r₀} dμ_A(a) < ∞`. Its other fields are `Ξ > 0`
  (`rationalXi_pos`), `σ ≥ 0`, and the two previous results.

## The statement

**`RationalSplitCenterHeightStatement`** (universe `u`): for every universe-`u`
nonarchimedean local field `F`, every connected reductive `G`, every split component
`s : T → G` (`IsSplitComponent s`, image `A_G(F)`), every `N ≥ 1` and every closed matrix
representation `ρ : G → GL_N` (`IsClosedSubgroup ρ`), with `σ = rationalHeight ρ`:

1. there is `C` with `1 + σ(a) ≤ C (1 + σ(a g))` for all `a ∈ A_G(F)` and `g ∈ G¹`; and
2. for every Haar measure `μ_A` on `A_G(F)` there is a real `r₀` with
   `∫⁻_{A_G(F)} ofReal((1 + σ(a))^{-r₀}) dμ_A(a) < ∞`.

### Why the statement holds

The statement has no structural premise, and it is true for every connected reductive `G`.
Write `H_G : G(F) → Hom(Rat(G), ℤ)` for the valuations of the rational characters; its kernel is
`G¹`.

- Every rational character `χ` satisfies `|log|χ(g)|_F| ≤ C_χ (1 + σ(g))` (the Library's
  `rationalNormCharacters_abs_log_rationalMatrixNorm_bound`). So `|H_G(g)| ≤ c (1 + σ(g))`.
- The restriction `Rat(G) → Rat(A_G)` has finite cokernel (I.1, p. 239). On the split torus
  `A_G(F) ≅ (F^×)^r`, the height `σ` is bounded above and below by affine functions of
  `|H_G|`, since `ρ ∘ s` is diagonalizable.
- For `a ∈ A_G(F)` and `g ∈ G¹`, `H_G(a g) = H_G(a)`. Hence
  `σ(a) ≤ c' (1 + |H_G(a)|) = c' (1 + |H_G(a g)|) ≤ c'' (1 + σ(a g))`, which is clause 1.
- `A_G(F) ∩ G¹` is compact (the Library's `isCompact_splitComponent_inf_commonNormKernel`) and
  open in `A_G(F)`. `H_G` embeds `A_G(F) / (A_G(F) ∩ G¹)` as a lattice of rank `r`. With the lower
  bound `1 + σ(a) ≥ c (1 + |H_G(a)|)`, the integral in clause 2 is at most a constant times
  `Σ_{λ ∈ ℤ^r} (1 + |λ|)^{-r₀}`, which is finite for `r₀ > r`.

This argument is not formalized here; the statement is the obligation.

### Correspondence with the source

- Clause 2 is what makes Waldspurger's integral `∫_{A_G} χ^{-1}(a) f(ag) da` absolutely convergent
  for `f ∈ C(G)` (VIII.4, "L'intégrale est absolument convergente"). In the Library this is the
  field `integrable` of `CentralWeights`.
- Clause 1 gives the hypothesis `hS` of the Library's
  `CentralWeights.enorm_centralProjection_le_rpow_neg` for `S = G¹`. That theorem is the estimate
  "on vérifie aisément" in the proof of Proposition VIII.4.1. The source states it for the
  elements `p_χ φ` of `p_χ(°C(G))`, `φ ∈ °C(G)`; the theorem gives it for `p_χ f` with any
  `f ∈ C(G)`.
- The statement quantifies over every split component and every closed `ρ`. Waldspurger's `A_G`
  is the largest central split torus, and his `σ` uses an embedding with `τ(K) ⊂ GL_n(𝒪)`.
- Provenance: derived. Both clauses are consequences of I.1 that the source uses implicitly in
  VIII.4.

## Consequences of the statement (section `Projection`)

- `RationalSplitCenterHeightStatement.centralWeights`: the actual `CentralWeights` for every Haar
  measure on `A_G(F)`.
- `RationalSplitCenterHeightStatement.exists_one_add_add_le`: there is `C > 0` with
  `1 + σ(g) + σ(a) ≤ C (1 + σ(a g))` for all `g ∈ G¹` and `a ∈ A_G(F)`. It follows from
  clause 1 and `σ(g) ≤ σ(a⁻¹) + σ(a g) = σ(a) + σ(a g)`.
- **`rationalCentralProjection hKo hKc hPK ρ muA hw hχ`** (definition): Waldspurger's `p_χ` on
  the actual `C(G)`, for a measure `μ_A` on `A_G(F)` with `hw : CentralWeights μ_A Ξ σ` and a
  unitary measurable character `χ` of `A_G(F)` (`IsUnitaryCharacter χ`), as a linear map
  `RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] (G(F) → ℂ)`. It is the Library's
  `Space.centralProjection`; `rationalCentralProjection_apply` gives
  `(p_χ f)(g) = ∫_{A_G(F)} χ(a)^{-1} f(a g) dμ_A(a)`.
- `RationalSplitCenterHeightStatement.enorm_rationalCentralProjection_le`: given the statement,
  for a connected reductive `G`, a split component, a closed `ρ`, a Haar measure `μ_A`, a unitary
  `χ`, `f ∈ C(G)` and `r ∈ ℝ`, there is a finite `c` with
  `|(p_χ f)(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` for every `g ∈ G¹`. It applies
  `CentralWeights.enorm_centralProjection_le_rpow_neg` with the two previous results.

The other generic results of `CentralProjection` (`centralProjection_mul_left`, i.e.
`p_χ f(b g) = χ(b) p_χ f(g)` for a right-invariant `μ_A`; `IsBiInvariant.centralProjection`,
which needs `A ≤ Z(G)`, given here by `IsCentral.range_le_center`) and of
`CentralProjectionFamily` apply to these data.

## Scope

- `RationalSplitCenterHeightStatement` is not proved here.
- The normalization of `μ_A` (Waldspurger: `mes(A_G ∩ K) = 1`) is not fixed; every Haar measure
  is allowed.
- Proposition VIII.4.1 (finite dimension of `p_χ(°C_H)`) and Theorem VIII.4.2 are not treated.
  The cusp forms `°C(G)` on actual points need the constant terms of III.6 for all standard
  parabolics, which are not treated here.
- Provenance: the statement is derived (see above). `rationalCentralProjection` is `p_χ` of VIII.4
  through the Library's generic `CentralProjection`. The remaining declarations are internal glue.
