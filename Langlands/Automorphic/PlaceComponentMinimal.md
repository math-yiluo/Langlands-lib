# Irreducible admissible stable subspaces by minimal multiplicity

Module `Langlands.Automorphic.PlaceComponentMinimal`, namespace
`Langlands.Automorphic.PlaceComponent`. Worker 174 wrote it as a step towards
`Langlands.Automorphic.CuspidalArchimedeanIrreducibleAdmissibleComponentStatement` (G1, Task 5992,
`8a7f44bc-c7bc-4ceb-96aa-6eff19b38f97`). Provenance: internal linear algebra about the Library
predicates `IsStable`, `IsIrreducible`, `intertwiners` and `IsAdmissible` of
`Langlands.Automorphic.CuspidalArchimedeanPlaceComponent`.

Throughout, `κ` is a representation of a group `K` and `π` a Lie action of `𝔤` on a complex
vector space `V`. A subspace is *stable* if both actions preserve it.

## Elementary facts

- `intertwiners_mono`: for `N ≤ M`, the intertwiners from a matrix representation `τ` into
  `N` are among those into `M`.
- `isStable_sInf`: an intersection of stable subspaces is stable.
- `isAdmissible_mono`: a subspace of an admissible subspace is admissible, by the previous
  inclusion and finite-dimensionality of subspaces of finite-dimensional spaces.

## Minimal multiplicity

`exists_isIrreducible_isAdmissible`. Hypotheses:

- `M` is a nonzero stable admissible subspace;
- `τ₀` is a continuous matrix representation of `K` that *detects* stable subspaces of `M`:
  every nonzero stable `N ≤ M` has a nonzero `τ₀`-intertwiner into it.

Conclusion: `M` contains an irreducible admissible stable subspace. `τ₀` need not be
irreducible.

Proof:

1. Among the nonzero stable `N ≤ M`, choose one for which `dim Hom_K(τ₀, N)` is minimal
   (`Nat.find`). The dimension is finite because `M` is admissible, and positive by detection.
2. Let `N₀` be the intersection of all stable subspaces containing the images of all
   `τ₀`-intertwiners into `N`. Then `N₀` is stable, `N₀ ≤ N`, and the `τ₀`-intertwiners into
   `N₀` are exactly those into `N`. So `N₀ ≠ ⊥`, by detection for `N`.
3. Let `W' ≤ N₀` be stable and nonzero. Its `τ₀`-intertwiners form a subspace of those of
   `N₀` of at least the minimal dimension, so the two spaces coincide
   (`Submodule.eq_of_le_of_finrank_le`).
4. Hence `W'` contains all the images, and so `N₀ ≤ W'`. Thus `N₀` is irreducible, and it is
   admissible as a subspace of `M`.

## Images under equivariant maps

Let `Φ : V → V'` be linear and equivariant for the compact and Lie actions on both sides.

- `injOn_of_isIrreducible`: if `W` is irreducible and `Φ(W) ≠ 0`, then `Φ` is injective on
  `W`. `W ⊓ ker Φ` is stable and not all of `W`.
- `isIrreducible_map`: if `W` is irreducible and `Φ(W) ≠ 0`, then `Φ(W)` is irreducible.
  Let `W' ≤ Φ(W)` be stable. Then `W ⊓ Φ⁻¹(W')` is stable in `W`, so it is `⊥` (and then
  `W' = ⊥`) or `W` (and then `W' = Φ(W)`).
- `isAdmissible_map`: if `W` is `K`-stable and admissible and `Φ` is injective on `W`, then
  `Φ(W)` is admissible. An intertwiner `T'` into `Φ(W)` is `Φ ∘ T`, where
  `T = (Φ|_W)⁻¹ ∘ T'`. `T` intertwines because `Φ` is injective on `W` and `W` is stable. So
  the intertwiners into `Φ(W)` lie in the image of the finite-dimensional space of
  intertwiners into `W` under left composition with `Φ`.
