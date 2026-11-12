# Vertices, facets and Harris's distinguished covering of Drinfeld's upper half space

Author: Worker 21.

The building of `PGL_{d+1}(F)` is the space `NormClass F (Fin (d + 1) → F)` of
norms up to homothety (module `DrinfeldReduction`). This module adds to it:

- the Goldman–Iwahori distance;
- vertices (classes of lattice norms) and facets (chains of lattices);
- the stars of vertices in the first barycentric subdivision and Harris's
  neighbourhoods `B(e, ε)`, `B(f, ε)`.

It then defines Harris's subsets `U(f) = Res⁻¹(B(f, ε))` of Drinfeld's upper
half space `Ω` and the stabilizers `S(f)`, and proves `γ U(f) = U(γ f)`. Whether
the `U(f)` are distinguished and form a covering with the nerve of the building
is not proved here (see Scope). All declarations lie in `Langlands.Analytic`.

## Original sources and derived provenance

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`, §2,
printed p.90 / PDF p.16: "We choose an admissible, GJ^ad-equivariant covering of Ω by
distinguished open subsets adapted to the map Res. For example, choose ε > 0,
and for each vertex e ∈ BT let B(e, ε) be the open ε-neighborhood of the star
of e in the first barycentric subdivision of BT. For the i-dimensional simplex f
with vertices e₀, e₁, …, e_i, we let B(f, ε) = B(e₀, ε) ∩ B(e₁, ε) ∩ ⋯ ∩
B(e_i, ε). Then for each facet e ⊂ BT the subset U(e) = Res⁻¹(B(e, ε)) ⊂ Ω is
distinguished, and the covering of Ω by the {U(e)} is admissible (cf. [BC])."
The same page: "for any facet e of BT, let S(e) be the stabilizer of e."

Rémy–Thuillier–Werner, *Bruhat-Tits buildings and analytic geometry*
(arXiv:1110.1362), registered as
`remy-thuillier-werner-2012-bruhat-tits-analytic-geometry`, SHA256
`f176a2657963c2e6da49a2e0282353097fff8ad67b7cf17f51c2372325591d0b`
(PDF page = printed page):

- p.14: "The 0-skeleton (i.e., the vertices) for the simplicial structure
  corresponds to the k°-lattices in the k-vector space V, that is the free
  k°-submodules in V of rank d + 1. To a lattice L is attached a norm ‖·‖_L by
  setting ‖x‖_L = inf{|λ| : λ ∈ k^× and λ⁻¹x ∈ L}. One recovers the k°-lattice L
  as the unit ball of the norm ‖·‖_L."
- p.15: in the apartment of a basis `e`, with norms
  `‖Σ λ_i e_i‖_{e,c} = max_i exp(c_i)|λ_i|`, "the inequations c₀ ⩽ c₁ ⩽ ⋯ ⩽ c_d
  and c_d − c₀ ⩽ −log|ϖ| define an alcove (whose boundary contains x) and any
  other alcove in A_e is obtained by using the action of the affine Weyl group".

The vertices of that alcove are the norms with `c = (0, …, 0, a, …, a)`,
`a = −log|ϖ|`. They form a chain `ν₀ ≤ ν₁ ≤ ⋯ ≤ ν_d ≤ |ϖ|⁻¹ ν₀`, that is, a
chain of unit-ball lattices `L₀ ⊇ L₁ ⊇ ⋯ ⊇ L_d ⊇ ϖ L₀`. Faces of alcoves are
subchains. This motivates the definition of facets below. The definitions of
facets, of the stars and of the neighbourhoods in the norm model are derived,
as explained next. They are not proved in Lean to agree with the simplicial
structure of the cited theorem.

### Derivation of the star

In apartment coordinates, write `D(x, y) = sup(x/y) · sup(y/x)` for two norms.
For norms diagonalized by one basis, `log D` is the spread `max_i (c_i − c'_i) −
min_i (c_i − c'_i)`. For a point `x` in a closed alcove with vertex `e`, the
barycentric coordinate of `e` is `1 − log_q D(x, e)`, with `q = |ϖ|⁻¹`.
Vertices outside the carrier of `x` have `log_q D(x, e') ≥ 1`. For example, in
the tree, the point at parameter `t` on the edge from `c = (0, 0)` to
`c = (a, 0)` has distances `t` and `1 − t` to the two ends, in units of `a`.

Hence the barycentric coordinates are `λ_e(x) = max(0, 1 − log_q D(x, e))`. The
closed star of `e` in the first barycentric subdivision is the set of points
where `λ_e` is maximal, that is, where `e` is a vertex nearest to `x` for `D`.
This computation is derived and is not formalized. Harris measures `B(e, ε)`
in the metric of the building. Here the Goldman–Iwahori distance `log D` is
used; this is a derived choice.

## Declarations

### Goldman–Iwahori distance (namespace `VectorNorm`)

For norms `ν, μ` on a vector space `V`:

- `ratioSup ν μ = ⨆ x, ofReal (ν x / μ x)` in `[0, ∞]`; `distRatio ν μ =
  ratioSup ν μ · ratioSup μ ν` (multiplicative form of the distance);
  `distRatio_comm`.
- `ratioSup_of_eq_mul_left/right`, `distRatio_of_eq_mul_left`,
  `Homothetic.distRatio_eq`: scaling a norm by `c > 0` multiplies the
  suprema by `c` and `c⁻¹`, so `distRatio` is invariant under homothety.
- `one_le_distRatio`, `ratioSup_self_le_one`, `distRatio_self`: for `V ≠ 0`,
  `distRatio ≥ 1`, with equality on the diagonal.
- `IsLatticeNorm ν`: every value `ν x` is the absolute value of a scalar.
  `IsLatticeNorm.eq_sInf`: then for `x ≠ 0`,
  `ν x = inf {|t| : t ≠ 0, ν(t⁻¹ x) ≤ 1}`, the formula `‖x‖_L` of the quotation
  for the unit ball `L` of `ν`.
- `IsLatticeChain ν` for `ν : Fin (k + 1) → VectorNorm F V`: all `ν i` are
  lattice norms, `ν i ≤ ν j` for `i ≤ j`, and `|t| ν_k ≤ ν₀` for every scalar
  with `|t| < 1`. For unit balls this is `L₀ ⊇ ⋯ ⊇ L_k ⊇ t L₀`.

### The building (namespace `NormClass`)

- `distRatio` on classes (well defined by `Homothetic.distRatio_eq`),
  `distRatio_mk`, `distRatio_comm`, `one_le_distRatio`, `distRatio_self`.
- `IsVertex x`: `x` is the class of a lattice norm.
- `IsFacet S`: `S` is the set of classes of a lattice chain;
  `IsFacet.isVertex`, and `isFacet_singleton` (a vertex is a facet).
- `vertexStar e = {x | ∀ e', IsVertex e' → distRatio x e ≤ distRatio x e'}`;
  `self_mem_vertexStar`.
- `vertexNbhd e ε = {x | ∃ y ∈ vertexStar e, distRatio x y < exp ε}`
  (Harris's `B(e, ε)`); `vertexStar_subset_vertexNbhd` for `ε > 0`.
- `facetNbhd S ε = ⋂ e ∈ S, vertexNbhd e ε` (Harris's `B(f, ε)`).

### Invariance under `GL_{d+1}(F)`

For the action `(γ • ν)(a) = ν(a γ)` of `DrinfeldReduction`:

- `VectorNorm.vecMulEquiv γ`: `a ↦ a γ` as a permutation of row vectors.
  `ratioSup_smul` reindexes the supremum along it. Then `distRatio_smul`,
  `IsLatticeNorm.smul`, `IsLatticeChain.smul`.
- `NormClass.distRatio_smul`, `IsVertex.smul`, `isVertex_smul_iff`,
  `IsFacet.smul`, `smul_mem_vertexStar_iff`, `smul_mem_vertexNbhd_iff`,
  `smul_mem_facetNbhd_iff`: `γ` maps stars, neighbourhoods and facets to those
  of the translated vertices.

### Harris's domains (namespace `DrinfeldUpperHalfSpace`)

- `facetDomain K S ε = reduction K ⁻¹' facetNbhd S ε : Set (Omega F K d)`
  (Harris's `U(f)`).
- `facetStabilizer S`: the stabilizer of `S` in `GL_{d+1}(F)` for the
  pointwise action on sets (Harris's `S(f)`).
- `actionMap_mem_facetDomain_iff` (with `[ProperSpace F] [NeZero d]`, as for
  the group action): `γ z ∈ U(γ f) ↔ z ∈ U(f)`, from `reduction_actionMap` and
  `smul_mem_facetNbhd_iff`.
- `actionMap_mem_facetDomain_of_mem_stabilizer`: `S(f)` preserves `U(f)`.

## Scope

Not proved here:

- that `IsVertex`, `IsFacet` and `vertexStar` agree with the simplicial
  structure of the building and its barycentric subdivision (derivation
  above);
- that the `U(f)` are distinguished, that they cover `Ω`, and that their nerve
  is the building;
- compactness of `S(f)` modulo the centre.
