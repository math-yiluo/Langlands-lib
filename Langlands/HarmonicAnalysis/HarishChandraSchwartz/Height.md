# The height function `σ` of a linear representation

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Height`,
namespace `Langlands.HarishChandraSchwartz`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, section I.1 (printed
p. 242, PDF p. 8). Waldspurger fixes an algebraic embedding `τ : G → GL_n(F)` with
`τ(K) ⊂ GL_n(𝒪)`, where `𝒪` is the ring of integers of `F`. For `g ∈ G` he writes
`τ(g) = (a_ij)` and `τ(g)⁻¹ = (b_ij)` and sets

`‖g‖ = sup_{i,j} sup(|a_ij|_F, |b_ij|_F)`,  `σ(g) = log ‖g‖`.

He records that `‖g‖ ≥ 1`, that `‖g₁ g₂‖ ≤ ‖g₁‖ ‖g₂‖`, and that `‖k₁ g k₂‖ = ‖g‖`
for `k₁, k₂ ∈ K`. The height `σ` is the second weight in the seminorms `ν_r` of
III.6 (`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic`).

## Scope

The construction is generic. `F` is any normed field. `τ : G →* GL ι F` is any
group homomorphism, for any nonempty finite index type `ι` (Waldspurger's `n ≥ 1`).
The properties of I.1 use the ultrametric inequality, written `[IsUltrametricDist F]`.
The topological statements give continuity or closed-embedding hypotheses on `τ`
explicitly. Here `GL ι F` carries Mathlib's topology on units, induced from
`A ↦ (A, A⁻¹)`.

This module does not construct Waldspurger's algebraic embedding of the rational
points of a reductive group, nor his maximal compact subgroup `K`. Instantiating
`τ` and proving that `τ` is a closed embedding are structural inputs for the
consuming modules. The hypothesis `τ(K) ⊂ GL_n(𝒪)` corresponds to
`K ≤ heightSubgroup τ`.

## Definitions

- `entryNorm A`: the largest absolute value of an entry of a square matrix `A`.
- `glNorm A = max (entryNorm A) (entryNorm A⁻¹)` for `A : GL ι F`. For `A = τ(g)`
  this is Waldspurger's `‖g‖`.
- `glNormLeOne`: the subgroup of `GL ι F` of elements of norm at most `1`, i.e.
  `GL_n(𝒪)` (all entries of `A` and `A⁻¹` in the closed unit ball).
- `height τ g = Real.log (glNorm (τ g))`, Waldspurger's `σ(g)`.
- `heightSubgroup τ`: the preimage `τ⁻¹(GL_n(𝒪))`.

## Results

Elementary facts:

- `norm_le_entryNorm`, `entryNorm_le`, `entryNorm_nonneg`, `entryNorm_one`.
- `norm_le_glNorm`, `norm_inv_le_glNorm`, `glNorm_le`, `glNorm_nonneg`.
- `glNorm_inv` (`‖A⁻¹‖ = ‖A‖`) and `glNorm_one`.

For an ultrametric absolute value:

- `entryNorm_mul_le`: `entryNorm (A B) ≤ entryNorm A · entryNorm B`. This is the
  ultrametric inequality applied to `(AB)_ij = Σ_k A_ik B_kj`.
- `glNorm_mul_le`: `‖g₁ g₂‖ ≤ ‖g₁‖ ‖g₂‖`, using `(AB)⁻¹ = B⁻¹ A⁻¹`.
- `one_le_glNorm`: `‖g‖ ≥ 1`. From `1 = entryNorm (A A⁻¹) ≤ ‖A‖²`.
- `glNorm_mul_mul_of_le_one`: `‖k A k'‖ = ‖A‖` when `‖k‖, ‖k'‖ ≤ 1`.
- `height_nonneg`, `height_mul_le` (`σ(gh) ≤ σ(g) + σ(h)`), `height_one`,
  `height_inv` (`σ(g⁻¹) = σ(g)`; the last two hold without the ultrametric
  hypothesis).
- `one_add_height_le`: `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))`. This is the inequality
  used in Waldspurger's proof of Lemma III.6.1 (printed p. 272, PDF p. 38).
- `height_mul_mul`: `σ(k g k') = σ(g)` for `k, k' ∈ τ⁻¹(GL_n(𝒪))`. This is
  Waldspurger's bi-`K`-invariance whenever `τ(K) ⊂ GL_n(𝒪)`.

Topology:

- `continuous_entryNorm`, `continuous_glNorm`; `continuous_height` for continuous
  `τ` (ultrametric `F`).
- `isCompact_entryNorm_le`, `isCompact_glNorm_le`: for proper `F` (for example a
  nonarchimedean local field), the sets `{A : ‖A_ij‖ ≤ R ∀ i j}` and `{‖A‖ ≤ R}`
  are compact. The second is the preimage of a compact set under the closed
  embedding `A ↦ (A, A⁻¹)`, intersected with the closed set `{glNorm ≤ R}`.
- `isOpen_glNormLeOne` (ultrametric `F`): `GL_n(𝒪)` is open. This holds because
  closed balls are open for an ultrametric absolute value.
- `isOpen_heightSubgroup` for continuous `τ`. For a closed embedding `τ` and
  proper `F`: `isCompact_heightSubgroup` and `isCompact_height_le` (every sublevel
  set `{σ ≤ N}` is compact). These are the hypotheses on `σ` used in the density
  theorem for test functions in `C(G)`.

## Provenance notes

Waldspurger states the three properties of `‖·‖` without proof ("On vérifie que").
The Lean proofs are the direct verifications. Compactness of the sublevel sets
and openness of `τ⁻¹(GL_n(𝒪))` are not stated in I.1. They are standard
consequences of the definitions, recorded here because the Schwartz-space
arguments of III.6 need them.
