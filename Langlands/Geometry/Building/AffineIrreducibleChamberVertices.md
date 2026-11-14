# Vertices of a chamber of an irreducible affine root system

Module `Langlands.Geometry.Building.AffineIrreducibleChamberVertices`, namespace
`Langlands.Geometry.Building.AffineRootSystem.IsAffineRootSystemWithRankZero`.

## Contents

The module combines two existing modules:

- `Langlands.Geometry.Building.AffineChamberVertexSimpleRoots`: the vertex–simple-root
  correspondence (KP Proposition 1.3.22(6)) and the transitivity corollary, all under the
  explicit hypothesis `hli` that the simple affine roots of the chamber are linearly independent;
- `Langlands.Geometry.Building.AffineIrreducibleSimpleRoots`: `linearIndependent_simpleAffineRoots`,
  which derives exactly `hli` from irreducibility `IsIrreducibleRoots Ψ` (KP Definition 1.3.13)
  (the linear-independence part of KP Proposition 1.3.22(5)).

Each result here is the corresponding result of `AffineChamberVertexSimpleRoots` with `hli`
replaced by `hirr : IsIrreducibleRoots Ψ`. Throughout, `Ψ : Set (A →ᵃ[ℝ] ℝ)` is a set of affine
functionals on a real affine space `A` over `V` (independent universes `uV`, `uA`),
`hΨ : IsAffineRootSystemWithRankZero Ψ` (the Library form of KP axioms AR 1–AR 4),
`hc : IsRegular Ψ c` (no root vanishes at `c`, so `facet Ψ c` is a chamber) and
`hne : Ψ.Nonempty`. Nonemptiness stays a separate hypothesis, since the empty set satisfies
`IsIrreducibleRoots` vacuously. `simpleVertex Ψ C ψ` is the definition from
`AffineChamberVertexSimpleRoots`: a chosen point of `A` at which every simple affine root of `C`
other than `ψ` vanishes, when such a point exists (under the hypotheses above it exists, is
unique, and `ψ` is positive there).

- `mem_facetClosure_and_isVertex_iff_of_isIrreducibleRoots hΨ hirr hc hne`:
  `x ∈ facetClosure Ψ c ∧ IsVertex Ψ x ↔
  ∃ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), x = simpleVertex Ψ (facet Ψ c) ψ`.
- `simpleVertexEquivOfIsIrreducibleRoots hΨ hirr hc hne :
  simpleAffineRoots Ψ (facet Ψ c) ≃ {x : A // x ∈ facetClosure Ψ c ∧ IsVertex Ψ x}`, with
  `coe_simpleVertexEquivOfIsIrreducibleRoots_apply` (it sends `ψ` to
  `simpleVertex Ψ (facet Ψ c) ψ`). This is KP Proposition 1.3.22(6) for irreducible `Ψ`.
- `apply_simpleVertex_of_isIrreducibleRoots`: for `e ∈ rootStabilizer Ψ` with
  `e '' facet Ψ c = facet Ψ c` and a simple affine root `ψ`,
  `e (simpleVertex Ψ (facet Ψ c) ψ) = simpleVertex Ψ (facet Ψ c) (ψ ∘ e⁻¹)`.
- `exists_mem_eq_comp_symm_of_subsingleton_of_isIrreducibleRoots`: let
  `Γ : Subgroup (A ≃ᵃ[ℝ] A)` with `Γ ≤ rootStabilizer Ψ`, every element of `Γ` mapping
  `facet Ψ c` onto itself, and `hfix`: the points of `facetClosure Ψ c` fixed by all of `Γ` form a
  subsingleton. Then for simple affine roots `ψ, η` of `facet Ψ c` there is `e ∈ Γ` with
  `η = ψ ∘ e⁻¹`.
- `exists_perm_chamberCartanMatrix_apply_eq_of_subsingleton`: with the same `Γ`, for any two
  simple affine roots `ψ, η` there is a permutation `σ` of the simple affine roots of `facet Ψ c`
  with `σ ψ = η` and
  `chamberCartanMatrix Ψ (facet Ψ c) (σ k) (σ l) = chamberCartanMatrix Ψ (facet Ψ c) k l` for all
  `k, l`. Here `chamberCartanMatrix` is the published integer Cartan matrix of the chamber
  (module `AffineChamberCartanMarks`, entries `ψ̇(η̇∨)`).

## Provenance

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 1.3.22(5)–(6)
  (printed p. 23, PDF p. 54): "Assume that Ψ is irreducible. … (6) The vertices
  `{x₀, …, x_ℓ}` of `C` are in bijection with `Δ` specified by `ψ_i(x_j) = 0` if `i ≠ j` and
  `ψ_i(x_i) > 0`." The first three results are (6) and its naturality, now with KP's
  irreducibility hypothesis (Definition 1.3.13, printed p. 18, PDF p. 49) in place of the
  explicit linear-independence hypothesis of `AffineChamberVertexSimpleRoots`.
- The transitivity results formalize a step in the proof of KP Theorem 10.3.1 (printed p. 392,
  PDF p. 423): there is "a natural Γ-equivariant bijective correspondence between the set of
  vertices of C and Δ", and Γ "acts transitively on the set of vertices of C, and hence it acts
  transitively on Δ". As in `AffineChamberVertexSimpleRoots`, the hypothesis used is that the
  `Γ`-fixed points of the closed chamber form a subsingleton. The last result combines this with
  the published covariance `exists_perm_chamberCartanMatrix_apply_eq` (module
  `AffineChamberCartanMarks`); this combination is internal glue.

## Proof notes

Every result is a direct application of the corresponding result of
`AffineChamberVertexSimpleRoots` to `hΨ.linearIndependent_simpleAffineRoots hirr hc`. The last
one feeds the transitivity statement into `exists_perm_chamberCartanMatrix_apply_eq` with the
underlying set of `Γ`.
