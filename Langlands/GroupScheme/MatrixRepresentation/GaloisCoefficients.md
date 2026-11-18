# Universal coefficients of representations of a scalar-extended group

This internal module continues `GaloisTwist`. Fix fields `k ⊆ K`, an affine
group scheme `G` over `Spec k` (`IsAffineHom G.X.hom`) and a finite free
representation `ρ` of `G_K = G ×_k K` on `Kⁿ`. Write `O(G)` for the published
coordinate algebra `CharacterUnits.Coord G` and `u` for its universal point
`CharacterUnits.universalPoint G`. The module expresses actual stability,
actual intertwining and Galois twisting through one matrix with entries in
`K ⊗[k] O(G)`. The universal matrix and its covariance under Galois twists
(entrywise `σ ⊗ id`, from `affineMatrix_galoisTwist_scalarPoint` of
`GaloisTwist`) are this module's own coordinate construction. They are built
from the Library's affine coordinates and base-change point equivalences. The
motivation is the projective Galois descent in the proof of Theorem 3.3 of
Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un
corps quelconque*, J. reine angew. Math. 247 (1971), pp. 203–204. That proof
uses a representation defined over `k` of a split form and a projective
intertwiner, not this coefficient description.

## Points of `G_K`

The test algebras `S` carry compatible `K`- and `k`-algebra structures
(`IsScalarTower k K S`).

- `scalarExtensionPoint_naturality`: the published scalar-extension point is
  natural for `K`-algebra maps `f : S → S'`. Restricting scalars of `f` acts on
  the underlying point of `G`. The proof applies the published
  `baseChangePointsEquiv_naturality` and `testIso_hom_comp_map`.
- `scalarBasePoint x` is the point of `G` underlying a point `x` of `G_K`, through
  the published test identification and pullback-point equivalence. Its
  inverse property is `scalarExtensionPoint_scalarBasePoint`.
- `universalScalarPoint K G` is the universal point of `G`, seen as a point of
  `G_K` over `K ⊗[k] O(G)` through `scalarPoint`.
- `universalMatrix ρ` is the matrix of `ρ` at `universalScalarPoint K G`. It is
  an `n × n` matrix over `K ⊗[k] O(G)`.
- `universalEval x : K ⊗[k] O(G) → A` is the `K`-algebra map `c ⊗ f ↦ c · x*(f)`,
  where `x*` is the published coordinate map `Lie.pointCoordinates G` of the
  base point.
- `universalScalarPoint_eval`: every point `x` of `G_K` over a compatible
  algebra `A` is the image of the universal scalar point along
  `universalEval x`. The proof uses naturality, `lift_comp_includeRight`, and
  the published `CharacterUnits.affinePointMap_universalPoint`.
- `affineMatrix_eq_universalEval` and `affineMatrix_eq_map_universalEval`: the
  matrix of `ρ` at `x` is the universal matrix with `universalEval x` applied
  to each entry. These follow from the published `affineMatrix_naturality`.
  `commAlgCat_ofHom_apply` is the unfolding used by that proof.

## Stability and intertwining

- `functional_mulVec_algebraMap` is the identity
  `L((M · v)_i) = (L(M) · v)_i` for a `K`-linear functional `L` and a constant
  vector `v`.
- `isStableSubspace_iff_universalMatrix`: a subspace `V ⊆ Kⁿ` is actually stable
  (the published all-test predicate `IsStableSubspace`) exactly when
  `L(universalMatrix ρ)` preserves `V` for every `K`-linear functional
  `L : K ⊗[k] O(G) → K`. Every test algebra `A` is given the `k`-structure
  through `K`, and the stability functional `ℓ` becomes `ℓ ∘ universalEval x`.
- `intertwines_iff_universalMatrix`: a constant matrix `C` actually intertwines
  `ρ` with `τ` (the published `Intertwines`) exactly when
  `C · universalMatrix ρ = universalMatrix τ · C` over `K ⊗[k] O(G)`.

## Galois twist

Fix `σ ∈ Aut_k(K)`.

- `universalMatrix_galoisTwist`: `universalMatrix (galoisTwist σ ρ)` is
  `universalMatrix ρ` with `σ ⊗ id` applied entrywise. This is the published
  formula `affineMatrix_galoisTwist_scalarPoint` at the universal point.
- `galoisTensor_symm_galoisTensor`, `galoisTensor_galoisTensor_symm` and
  `galoisTensor_smul` are elementary facts about `σ ⊗ id` on `K ⊗[k] R`:
  `σ⁻¹ ⊗ id` is its inverse, and `(σ ⊗ id)(c z) = σ(c) (σ ⊗ id)(z)`.
- `untwistFunctional R σ L` is the `K`-linear functional
  `σ ∘ L ∘ (σ⁻¹ ⊗ id)`. By `untwistFunctional_galoisTensor`, it sends
  `(σ ⊗ id)(z)` to `σ(L z)`.
- `universalMatrix_galoisTwist_map_untwist`: the coefficient of the twisted
  universal matrix at `untwistFunctional σ L` is the coefficient of
  `universalMatrix ρ` at `L` with `σ` applied entrywise. So every coefficient
  matrix of `ρ`, conjugated by `σ`, is a coefficient matrix of `ρ^σ`.
- `galoisComap σ V` is the `K`-subspace `{w | σ ∘ w ∈ V}`, which is `σ⁻¹(V)`.
- `IsIrreducible.galoisTwist`: the twist of an irreducible representation is
  irreducible. A stable subspace `V` of `ρ^σ` gives the stable subspace
  `galoisComap σ V` of `ρ`, by the previous identity and
  `RingHom.map_mulVec`. Then `V` is `0` or `Kⁿ` because `σ` is bijective.
- `Intertwines.galoisTwist`: if `C` intertwines `ρ` with `τ`, then `σ(C)`
  intertwines `ρ^σ` with `τ^σ`. The proof applies `σ ⊗ id` to the universal
  intertwining identity, using `(σ ⊗ id)(c ⊗ 1) = σ(c) ⊗ 1`.

No separability, Galois, smoothness, reducedness or characteristic assumption
is made. The test algebras include all nonreduced ones.
