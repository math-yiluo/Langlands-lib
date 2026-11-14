# Chamber transitivity from a group with at most one fixed point

Module `Langlands.Geometry.Building.AffineIrreducibleChamberTransitivity`.

## Contents

The module rewrites the transitivity results of
`Langlands.Geometry.Building.AffineIrreducibleChamberVertices` in the forms of the predicates
`HasTransitiveSimpleRoots` (module `Langlands.Geometry.Building.AffineTransitiveRootLengths`)
and `Langlands.GroupScheme.AffineCartan.IsVertexTransitive` (module
`Langlands.GroupScheme.SimplyConnected.AffineCartanTransitiveShape`). It also gives a
fixed-point criterion in terms of linear parts, and a version for the image of a group
homomorphism into the affine automorphisms of `A`.

Throughout, `V` is a real vector space, `A` is an affine space under `V` (independent universes
`uV`, `uA`), `Ψ : Set (A →ᵃ[ℝ] ℝ)` satisfies `hΨ : IsAffineRootSystemWithRankZero Ψ` (the
Library form of KP axioms AR 1–AR 4), `c : A` is a regular point (`hc : IsRegular Ψ c`),
`facet Ψ c` is its chamber and `facetClosure Ψ c` the closed chamber. The predicates used are:

- `HasTransitiveSimpleRoots Ψ C`: for any two simple affine roots `ψ, η` of `C` there is
  `e ∈ rootStabilizer Ψ` with `η = ψ ∘ e`.
- `IsVertexTransitive B` for an integer matrix `B` indexed by a finite type: for any two indices
  `i, j` there is a permutation `σ` with `B (σ k) (σ l) = B k l` for all `k, l` and `σ i = j`.
- `chamberCartanMatrix Ψ C` (module `AffineChamberCartanMarks`), indexed by the simple affine
  roots of `C`, has entry `ψ̇(η̇^∨)` at `(ψ, η)`.

### Results

- `fixedPoints_subsingleton_of_linear hlin`: for a set `Γ` of affine automorphisms of `A` such
  that the only vector `v : V` with `e.linear v = v` for all `e ∈ Γ` is `v = 0`, the set of
  points fixed by every `e ∈ Γ` is a subsingleton.

In the following, `hirr : IsIrreducibleRoots Ψ` (KP Definition 1.3.13) and `hne : Ψ.Nonempty`;
`Γ` is a subgroup of `A ≃ᵃ[ℝ] A` with `hΓ : Γ ≤ rootStabilizer Ψ`, every element of `Γ` maps
the chamber `facet Ψ c` onto itself (`hΓC`), and the points of the closed chamber fixed by all of
`Γ` form a subsingleton (`hfix`).

- `hasTransitiveSimpleRoots_of_subsingleton hΨ hirr hc hne Γ hΓ hΓC hfix`:
  `HasTransitiveSimpleRoots Ψ (facet Ψ c)`.
- `isVertexTransitive_chamberCartanMatrix_of_subsingleton hΨ hirr hc hne Γ hΓ hΓC hfix`
  (with `[Fintype (simpleAffineRoots Ψ (facet Ψ c))]`):
  `AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c))`.
- `chamberTransitivity_of_hom_of_linear hΨ hirr hc hne ρ hρ hρC hlin`: for a group `M` (any
  universe `uM`) and a group homomorphism `ρ : M →* (A ≃ᵃ[ℝ] A)` such that every `ρ m` lies in
  `rootStabilizer Ψ` (`hρ`) and maps `facet Ψ c` onto itself (`hρC`), and such that the only
  vector fixed by the linear parts of all `ρ m` is `0` (`hlin`), both conclusions hold:
  `HasTransitiveSimpleRoots Ψ (facet Ψ c)` and
  `AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c))`.

The hypotheses are kept explicit. The module does not construct a Galois action on an apartment,
does not prove that it stabilizes a chamber, and does not prove that its linear parts have no
nonzero common fixed vector.

## Provenance

The module is derived. It formalizes the transitivity step in the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Theorem 10.3.1 (printed p. 392, PDF p. 423). There
`C` is a `Γ`-stable chamber and `C^Γ = {x}`. Because `B(G)` contains no facet of positive
dimension, `Γ` acts transitively on the vertices of `C` (KP 9.2.4). The natural `Γ`-equivariant
bijection between the vertices of `C` and the basis `Δ` then makes `Γ` act transitively on `Δ`,
and hence the automorphisms of the affine Dynkin diagram of `Δ` act transitively on `Δ`. The
vertex statement is KP Proposition 1.3.22(6) (printed p. 23, PDF p. 54). The published results of
`AffineIrreducibleChamberVertices` already prove these steps; this module only restates them in
the forms `HasTransitiveSimpleRoots` and `IsVertexTransitive`, where the Cartan-matrix symmetry
stands for the diagram automorphism. The linear-part criterion and the homomorphism form are
internal glue: two common fixed points differ by a common fixed translation vector. No new
literature statement is transcribed.

## Proof notes

- `fixedPoints_subsingleton_of_linear`: for common fixed points `x, y` and `e ∈ Γ`,
  `e.linear (y -ᵥ x) = e y -ᵥ e x = y -ᵥ x` (`AffineMap.linearMap_vsub`). So `y -ᵥ x = 0` by
  `hlin`, hence `x = y`.
- `hasTransitiveSimpleRoots_of_subsingleton`: the published
  `exists_mem_eq_comp_symm_of_subsingleton_of_isIrreducibleRoots` gives `e ∈ Γ` with
  `η = ψ ∘ e⁻¹`. Then `e⁻¹ ∈ rootStabilizer Ψ`, because `Γ ≤ rootStabilizer Ψ` and subgroups are
  closed under inverses.
- `isVertexTransitive_chamberCartanMatrix_of_subsingleton` is the published
  `exists_perm_chamberCartanMatrix_apply_eq_of_subsingleton`, unfolded into the definition of
  `IsVertexTransitive`.
- `chamberTransitivity_of_hom_of_linear` applies the two previous results to `Γ = ρ.range`. The
  fixed-point hypothesis follows from `fixedPoints_subsingleton_of_linear` for the set
  `ρ.range`, restricted to the closed chamber (`Set.Subsingleton.anti`).
