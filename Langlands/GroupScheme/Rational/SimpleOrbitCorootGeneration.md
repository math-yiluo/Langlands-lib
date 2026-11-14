# Coroot products of Galois-equivariant unit families lie in `G(k)^+`

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.SimpleOrbitCorootGeneration`.

## Setting

- `D : GaloisCompatiblePinningData k K G` with pinning `p = D.pinning`, simple-root action
  `D.action` of `Γ = Aut_k(K)`, and normalized simple-root maps `D.rootMaps`.
- `t : S ⟶ D.torus`, and `i = groupHom t ≫ D.inclusion`.
- `relativeRootGeneratedExtension k K i` is the image of `G(k)^+` under scalar extension
  `G(k) → G(K)` (module `Rational.OrthogonalOrbitDescent`).

The theorems about `D` assume:
- `G` is smooth, connected reductive and locally of finite type;
- `D.torus` is affine and locally of finite type, and `(D.torus)_K` is split (`hT`);
- `K/k` is finite Galois;
- `i` is a maximal split torus (`hf`);
- `D.inclusion` is a closed subgroup (`hjc`) representing the centralizer of `i` (`hcent`);
- the simple coroots span the cocharacter lattice (`hspan`);
- the simple-root action is pairing-compatible (`hρ : IsPairingCompatible p.base D.action`,
  module `LinearAlgebra.RootDatumOrbitPairs`): each Galois element acts through a
  permutation of all roots preserving the integral pairing.

## Results

- `SplitPinning.orbitCoroot_eq_map_simpleCorootProduct`. Let `O` be a pairwise orthogonal set of
  simple roots, and `u` a unit family with `u b = 1` for `b ∉ O`. Then the orbit coroot
  product `orbitCoroot u` (module `Rational.OrthogonalOrbitCorootWords`) equals
  `p.inclusion(simpleCorootProduct u)`.
  - Proof: the coroot value of the rank-one data at `b` is by definition the image of
    `simpleCorootPoint b`. The commuting product over `O` maps to the torus product
    (`Finset.map_noncommProd`, `Finset.noncommProd_eq_prod`). Factors off `O` are `1`
    (`Finset.prod_filter_of_ne`, `Finset.prod_subtype`).
- `simpleOrbit b`: the Galois orbit `{σ b}` of a simple root `b`. `action_mem_simpleOrbit_iff`:
  the orbit is Galois-stable.
- `simpleCorootProduct_mem_of_isOrthogonal` (**orthogonal orbits**). If `b` is orthogonal to
  every `σ b ≠ b`, then every orbit family `c` at `b` (`IsOrbitFamily`, module
  `Rational.A2OrbitGeneration`) satisfies
  `p.inclusion(∏_x x^∨(c x)) ∈ relativeRootGeneratedExtension k K i`.
  - The orbit is pairwise orthogonal: `σ b` and `τ b` have the pairings of `b` and
    `σ⁻¹τ b`, by `hρ`.
  - Its roots restrict to one relative root `a`: `exists_relativeRoot_restrict` and
    `restrictMap_comp_root_action`. Also `-a` is a relative root (`relativeRootNegation`).
  - Apply `orbitCoroot_mem_map_relativeRootGeneratedSubgroup` and the bridge above.
- `simpleCorootProduct_mem_of_not_isOrthogonal` (**`A₂` orbits**). The conclusion is the same
  when some `σ₀ b ≠ b` is not orthogonal to `b`. One more hypothesis `hnc` is needed: for
  distinct Galois-conjugate simple roots `x`, `y` with both pairings `-1`, the points
  `x_x(1)` and `x_y(1)` do not commute.
  - The pairings are `-1` and `b + σ₀ b` is a root `m₀`: Library
    `pairing_eq_neg_one_of_not_isOrthogonal` and `exists_root_eq_add_of_not_isOrthogonal`.
  - Assemble the piece hypotheses of `simpleCorootProduct_mem_of_a2` (module
    `Rational.A2OrbitUnits`):
    - the restriction `a` as above;
    - `hline` from `restrictsToMultipliableLine`, with opposite factor pairs from
      `rootRankOneFactorization` and `hasRankOneFactorization_iff_hasOppositeFactorPairs`;
    - merged maps from `exists_mergedPieces`.
  - The base roots of the piece family are `g b` and `g σ₀ b`, where `g` is the chosen
    element `pairElement (basePair m₀)`. They are conjugate under `g σ₀ g⁻¹`. An orbit family
    at `b` is an orbit family at `g b`.
- `simpleCorootProduct_mem_of_isOrbitFamily`: combine the two cases by the dichotomy on `b`.
- `simpleCorootProduct_mem_of_equivariant` (**all equivariant families**). For every unit
  family `c` with `c(σ b) = σ(c b)`, assuming `hnc`, the image `p.inclusion(∏_b b^∨(c b))` lies
  in `relativeRootGeneratedExtension k K i`.
  - Proof: induction on the number of `b` with `c b ≠ 1`. Pick such `b` and split
    `c = c₁ c₂`, where `c₁` is `c` on the Galois orbit `O` of `b` and `1` off it, and `c₂` is
    `1` on `O` and `c` off it.
  - `c₁` is an orbit family at `b`. The family `c₂` is equivariant and has fewer non-unit
    values. Conclude with `simpleCorootProduct_mul`.

## Provenance

These are internal lemmas, built from published Library results, the accepted helper
modules of this task (`Rational.OrthogonalOrbitDescent`, `Rational.A2OrbitUnits` and their
imports) and Worker 185's accepted coordinate modules. The orbit dichotomy is the Library's
`Langlands.LinearAlgebra.RootDatumOrbitPairs`. They make no new mathematical assertion beyond
the stated Lean theorems.
