# Lemma II.1.5 of Waldspurger on actual rational points, from the upper bound of Lemma II.1.1

Author: Worker 5, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound`,
namespace `Langlands.HarishChandraSchwartz`.

The module proves

**`rationalXiSquareIntegrable_of_upperBound :
RationalXiUpperBoundStatement.{u} → RationalXiSquareIntegrableStatement.{u}`**.

So the Library's statement of Lemma II.1.5 on actual points (`RationalXiSquareIntegrableStatement`,
module `RationalXiSquareIntegrable`) follows from the Library's statement of the upper bound of
Lemma II.1.1 (`RationalXiUpperBoundStatement`, module `RationalXiUpperBoundStatement`). Both
statements are unchanged. The upper bound is not proved here (its proof is the separate Task 5326),
so Lemma II.1.5 is proved only conditionally on it. Every other ingredient of Waldspurger's proof
is proved in this module or already proved in the Library. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The recorded declaration is the definition `rationalCartanCell` of the cells used in the proof. The
other declarations are theorems.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The quotations were checked against the text of
PDF pages 7, 8 and 18.

- I.1, printed p. 241: "`G = ⋃_{m ∈ M̄_0^+/M_0^1} KmK`. (4)" and "il existe `C_1, C_2 > 0` tels
  que, pour tout `m ∈ M̄_0^+`, `C_1 δ_0(m)^{-1} ⩽ mes(KmK) ⩽ C_2 δ_0(m)^{-1}`, (5)". The proof of
  (5) chooses a smaller compact open `H` and uses
  `mes(HmH) ⩽ mes(KmK) ⩽ [K : H]^2 mes(HmH)` and `mes(HmH) = mes(H)[H : mHm^{-1} ∩ H]`.
- I.1, printed p. 242: "Il existe `C_1, C_2 > 0` tels que pour tout `m ∈ M_0`,
  `C_1(1 + |H_0(m)|) ⩽ 1 + σ(m) ⩽ C_2(1 + |H_0(m)|)`. (6)"
- Lemme II.1.1, printed p. 251: `Ξ(m) ⩽ C_2 δ_0(m)^{1/2}(1 + σ(m))^d` for `m ∈ M̄_0^+` (the
  second inequality).
- Lemme II.1.5, printed p. 252: "Il existe `d ∈ ℕ` tel que l'intégrale
  `∫_G Ξ(g)^2 (1 + σ(g))^{-d} dg` soit convergente." Proof: "D'après I.1 (4), il suffit de
  prouver qu'il existe `d ∈ ℕ` tel que la série
  `Σ_{m ∈ M̄_0^+/M_0^1} mes(KmK) Ξ(m)^2 (1 + σ(m))^{-d}` soit convergente. Grâce à I.1 (5) et au
  Lemme II.1.1, on est ramené à prouver que la série `Σ_{m ∈ M̄_0^+/M_0^1} (1 + σ(m))^{-d}` est
  convergente pour `d` assez grand. Ou encore, d'après I.1 (6) que la série
  `Σ_{H ∈ H_0(M̄_0^+)} (1 + |H|)^{-d}` l'est. C'est clair puisque `H_0(M_0)` est un réseau de
  `a_0`."

Renard, *Représentations des groupes réductifs p-adiques*, V.5.1 (Cartan decomposition) and V.5.2
(simultaneous standard basis), as itemized in the Library's note
`notes/renard/chapter-v-structural-inputs.md` (rows S19–S23). These are the structural hypotheses
of `RationalXiSquareIntegrableStatement`; this module uses them and does not prove them.

## Setting and notation

As in `RationalXiSquareIntegrable.md`: `F` is a nonarchimedean local field, `G` a connected
reductive group scheme over `Spec F`, `i : S → G` a maximal split torus, `ν` a generic cocharacter,
`P₀(F) = standardParabolicPoints i ν ∅`, `δ₀ = rationalMinimalModulus i ν`,
`Ξ = rationalXi hKc hPK`, `σ = rationalHeight ρ`, with the local instances of `RationalWeights` on
`G(F) = rationalPoints G`. For a cocharacter `y` of `S`, `ϖ^y = uniformizerPowers i (.ofAdd y)` is
the image in `G(F)` of `y(ϖ)`, `ϖ` the Library's uniformizer. A cocharacter `y` is *dominant* if
`simpleRootPairing i ν β y ≥ 0` for every simple relative root `β`. Then `|β(ϖ^y)|_F ≤ 1`, so
`ϖ^y ∈ M̄_0^+`.

## Declarations

### Cells (section `Cells`)

- **`rationalCartanCell i K0 F0 y`** (definition): the set of `k₁ ϖ^y f k₂` with `k₁, k₂ ∈ K0` and
  `f ∈ F0`, that is `⋃_{f ∈ F0} K0 ϖ^y f K0`, for a subgroup `K0` of `G(F)`, a finite set `F0` of
  points of the centralizer of `S` and a cocharacter `y`.

  It plays the role of Waldspurger's `KmK`. The Library's covering clause
  `FiniteCartanCovering F i ν K0` (Renard V.5.1 (4)) writes every `g` as `k₁ f a k₂` with `f ∈ F0`
  and `a` in the dominant uniformizer chamber `C_A^+` of `S(F)`. So `M̄_0^+/M_0^1` is replaced by
  the pairs `(y, f)` with `y` dominant and `f ∈ F0`. (Background, not used in Lean: `F0` plays
  the role of representatives of the finite group `M_0/M_0^1 A_0`.) Two such cells may overlap. This does not matter: only the covering and
  upper bounds are used.

### Translates (section `Translates`, generic topological groups)

- `exists_finset_mul_mem_of_isCompact`: a compact set `C` in a topological group is covered by
  finitely many sets `c⁻¹ K`, `K` an open subgroup (from Mathlib's
  `compact_covered_by_mul_left_translates`).
- `exists_measure_cell_le_doubleCoset`: for a left-invariant measure `μ`, a compact open subgroup
  `K0`, a finite family `φ(f)`, `f ∈ F0`, there is `N` with
  `μ(⋃_{f ∈ F0} K0 w φ(f) K0) ≤ N μ(K0 w K0)` for every `w` commuting with all `φ(f)`. Proof:
  `K0 w φ(f) K0 = φ(f) (φ(f)⁻¹ K0 φ(f)) w K0`. The compact set `φ(f)⁻¹ K0 φ(f)` lies in finitely
  many `c⁻¹ K0`, so the cell lies in finitely many left translates of `K0 w K0`, each of measure
  `μ(K0 w K0)`. `N` does not depend on `w`.

### Bounds on the cells (section `Bounds`)

- `exists_mem_rationalCartanCell`: from the covering clause, every `g ∈ G(F)` lies in
  `rationalCartanCell i K0 F0 y` for some dominant `y`. The point `a ∈ C_A^+` is `ϖ^y` for a
  dominant `y` (Library `exists_cocharacter_of_mem_CAplus`). The centralizer point `f` commutes
  with `ϖ^y` (`centralizerPoints_le_pointCentralizer`), so `k₁ f ϖ^y k₂ = k₁ ϖ^y f k₂`.
- `exists_rationalHeight_uniformizerPowers_le`: for compact `K0` and finite `F0` there is `B` with
  `σ(ϖ^y) ≤ σ(g) + B` for every `y` and every `g` in the cell of `y`. Proof:
  `ϖ^y = k₁⁻¹ g k₂⁻¹ f⁻¹`, subadditivity `rationalHeight_mul_le`, `σ(h⁻¹) = σ(h)`, and
  boundedness of the continuous `σ` on `K0` and on `F0⁻¹`.
- `exists_rationalXi_le_of_mem_rationalCartanCell`: assume a bound `Ξ(g₁ a g₂) ≤ C Φ(a)` for all
  `a` in some set `P`, with `C` depending on `g₁, g₂`. Then there is one `M` with
  `Ξ(g) ≤ M Φ(ϖ^y)` for every `y` with `ϖ^y ∈ P` and every `g` in the cell of `y`. Proof: cover
  `K0` by finitely many `c⁻¹ K` (`K` the compact open subgroup defining `Ξ`), write
  `k₁ ϖ^y f k₂ = (c₁ k₁⁻¹)⁻¹ (c₁ ϖ^y (f c₂⁻¹)) (c₂ k₂)` with `c₁ k₁⁻¹, c₂ k₂ ∈ K`, use the
  bi-`K`-invariance `rationalXi_mul_mul`, and take for `M` the maximum of the finitely many
  constants for `(g₁, g₂) = (c₁, f c₂⁻¹)`. This replaces Waldspurger's bi-`K`-invariance step:
  `K0` and `K` need not be equal, and `σ` need not be `K`-invariant.

### Volume bound I.1 (5) in `G(F)` (section `Volume`)

- **`exists_measure_doubleCoset_uniformizerPowers_le hi hK0o hK0c hbasis μ`**: for a compact open
  `K0` with `SimultaneousStandardBasisAt i ν K0` and a Haar measure `μ` on `G(F)`, there is `C`
  with `μ(K0 ϖ^y K0) ≤ C δ₀(ϖ^y)⁻¹` for every dominant `y`. This is the upper bound of I.1 (5),
  for `m = ϖ^y`, in `G(F)` itself.

  Proof, following Waldspurger's proof of (5): take a member `L ≤ K0` of the basis that is
  compatible with `P₀` (the parabolic for the empty set of simple roots). The Library's
  `standardBasisMember_rayIndex` gives `[L : L ∩ ϖ^y L ϖ^{-y}] ≤ δ_U(ϖ^y)⁻¹`, where `δ_U` is the
  Haar modulus of conjugation on `U₀(F)` restricted to the centre of the Levi `M₀(F)`. It equals
  `δ₀(ϖ^y)` by `Jacquet.closedRestrictCharacter_congr` (same unipotent group via `rootSet_empty`).
  The Library's `measure_doubleCoset_bounds` gives
  `μ(K0 ϖ^y K0) ≤ [L : L ∩ ϖ^y L ϖ^{-y}] [K0 : L] μ(K0)`. So `C = [K0 : L] μ(K0)`.

  The Library's `rationalLatticeQuotientVolume` proves upper volume bounds for lattice cells
  modulo the full centre. The present lemma is the bound in `G(F)` itself.

### The lower bound of I.1 (6) (section `Norm`)

- `exists_abs_latticePairing_le i hi ρ hρ α`: for a closed subgroup `i : S → G`, a closed matrix
  representation `ρ` and a character `α` of `S`, there is `C > 0` with
  `|⟨α, y⟩| ≤ C (1 + σ(ϖ^y))` for every cocharacter `y`. Proof: `|α(y(ϖ))|_F = q^{-⟨α, y⟩}`
  (`characterNorm_latticeSection`), and `|log |χ(s)|_F| ≤ C' (1 + σ(s))` for a rational character
  `χ` of the closed subgroup `S` (`rationalNormCharacters_abs_log_rationalMatrixNorm_bound` applied
  to the restriction of `ρ` to `S`, with `rationalMatrixNorm_restrict`). Divide by `log q > 0`.
- **`exists_cocharacterCoordinates_norm_le i hS hi ρ hρ`**: for a closed split torus `i : S → G`
  and a closed `ρ`, there are a finite type `I`, an injective map `H` from the cocharacters of `S`
  into the lattice `ℤ^I` in `ℝ^I` (the submodule `span ℤ` of the standard basis, sup norm), and
  `C > 0` with `1 + ‖H(y)‖ ≤ C (1 + σ(ϖ^y))` for every `y`. `H` is a coordinate isomorphism
  `X_*(S) ≅ ℤ^I` (`IsSplitTorus.exists_cocharacterCoordinates`). Since the pairing
  `X^*(S) × X_*(S) → ℤ` is perfect (`latticePairing_isPerfPair`), each coordinate is `⟨α_k, ·⟩`
  for a character `α_k`, bounded by the previous lemma.

  This is the left inequality of I.1 (6) at `m = ϖ^y`, with the lattice `H_0(A_0) ≅ X_*(S)` and
  a norm on `ℝ^I` in place of Waldspurger's Weyl-invariant Euclidean norm on `a_0`. All norms on
  `ℝ^I` are equivalent, so only the constant changes. The right inequality of (6) is not needed.

### Lemma II.1.5 (section `Main`)

**`rationalXiSquareIntegrable_of_upperBound h`**. Given the hypotheses of
`RationalXiSquareIntegrableStatement`, take `F0` from the covering clause and a compatible split
component `q` of `M₀` from the basis property. The proof applies the Library's generic
`CartanSquareBound.squareIntegrableWeight` (module `SquareIntegrability`), which proves
`SquareIntegrableWeight μ Ξ σ` from the following data. The index set is the dominant cocharacters
`y`. The cells are `rationalCartanCell i K0 F0 y`. The lattice is `ℤ^I` with the map `H` above.
And `δ(y) = δ₀(ϖ^y)`. Here `ϖ^y` lies in the chamber `standardComponentCAplus i ν ∅ q`
(`uniformizerPowers_mem_standardComponentChambers`), hence in `P₀(F)`
(`mem_standardParabolicPoints_of_mem_standardComponentCAplus`). The fields of `CartanSquareBound`
are proved as follows.

- Countability: the cocharacter lattice embeds in `ℤ^I`.
- Covering (I.1 (4)): `exists_mem_rationalCartanCell`.
- `σ ≥ 0`: `rationalHeight_nonneg`. `δ > 0`: `δ₀` takes values in units.
- Volume (I.1 (5)): `μ(cell y) ≤ N μ(K0 ϖ^y K0) ≤ N C δ₀(ϖ^y)⁻¹`, from
  `exists_measure_cell_le_doubleCoset` (`f ∈ F0` commutes with `ϖ^y`) and
  `exists_measure_doubleCoset_uniformizerPowers_le`.
- `Ξ` bound (Lemma II.1.1): `h` gives `d` and, for all `g₁, g₂`, a constant `C` with
  `Ξ(g₁ a g₂) ≤ C δ₀(a)^{1/2} (1 + σ(a))^d` on the chamber.
  `exists_rationalXi_le_of_mem_rationalCartanCell` turns this into
  `Ξ(g) ≤ M δ₀(ϖ^y)^{1/2} (1 + σ(ϖ^y))^d` on the cell of `y`. Then
  `exists_rationalHeight_uniformizerPowers_le` gives `1 + σ(ϖ^y) ≤ (1 + B') (1 + σ(g))` with
  `B' = max B 0`. So `|Ξ(g)| ≤ max M 0 (1 + B')^d δ₀(ϖ^y)^{1/2} (1 + σ(g))^d` (with `Ξ > 0`,
  `rationalXi_pos`).
- Norm bound (I.1 (6)): `1 + ‖H(y)‖ ≤ C_H (1 + σ(ϖ^y)) ≤ C_H (1 + B') (1 + σ(g))`.
- Injectivity of `H`.

The generic theorem then gives the convergence of the lattice series
`Σ_y (1 + ‖H(y)‖)^{-s}` for `s` larger than the rank (`summable_one_add_norm_rpow_neg`). This is
the last step of the source's proof.

## Correspondence with the source and differences

- The route is Waldspurger's: reduce to cells by I.1 (4), then bound each cell by I.1 (5), the
  upper bound of II.1.1 and the lower bound of I.1 (6), and sum over the lattice.
- Cells: the integral is not rewritten as a series. The generic theorem bounds the integral over
  each cell and sums, so overlapping cells are harmless.
- `K0`, `K` and `ρ`: the structural group `K0` (covering and basis) is not assumed equal to the
  group `K` defining `Ξ`, and `ρ(K) ⊂ GL_N(𝒪)` is not assumed. So `Ξ` and `σ` are not constant on
  the cells. The lemmas of section `Bounds` move the bounds from `ϖ^y` to the whole cell with
  constants independent of `y`. Waldspurger instead uses bi-`K`-invariance with `K0 = K`.
- I.1 (5) is proved here only as an upper bound and only at the points `ϖ^y`, which is all the
  proof uses. I.1 (6) is proved only as the lower bound for `|H|`.
- Provenance: derived. The main theorem proves the implication between two published Library
  statements by the source's argument. The definition `rationalCartanCell` and the lemmas of
  sections `Translates`, `Bounds` and `Norm` are internal adaptations needed because the Library's
  structural inputs give the Cartan decomposition in the form `K0 f ϖ^y K0`.

## Scope

- Lemma II.1.5 is proved only conditionally on `RationalXiUpperBoundStatement`.
- The structural hypotheses (`SimultaneousStandardBasisAt`, `FiniteCartanCovering`) remain
  hypotheses of `RationalXiSquareIntegrableStatement`. They are not proved here.
- The lower bound of I.1 (5) and the upper bound of I.1 (6) are not formalized here.
