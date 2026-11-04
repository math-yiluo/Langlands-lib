# The open cell and the Levi decomposition on rational points

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints`,
namespace `Langlands.HarishChandraSchwartz`.

The published modules `OpenCellIntegration` and `ParabolicHaar` prove Waldspurger's
integration formulas for abstract data. Two of their hypotheses are topological facts about
the group of `F`-points:

- `hι` of `OpenCellIntegration`: the open-cell map `(p, v) ↦ p v⁻¹` is an open embedding
  `P × V → G`;
- `hhomeo` of `leviUnipotentMeasure_isHaarMeasure` in `ParabolicHaar`: the coordinates
  `(m, u) ↦ m u` are a homeomorphism `M × U → P`.

This module proves both facts for the dynamic subgroups `P_G(χ)`, `U_G(χ⁻¹)`, `Z_G(χ)`,
`U_G(χ)` of an affine group scheme `G` over a topological field `k`. The group `G(k)` carries
the published rational-point topology, and the subgroups carry the subspace topology.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082,
I.1, printed p. 240 (PDF p. 6). For a semi-standard parabolic subgroup `P = MU` of `G` and
`f ∈ C_c^∞(G)`, formula (2) reads

`∫_G f(g) dg = ∫_{U×M×K} f(umk) δ_P(m)^{-1} dk dm du`,
`∫_G f(g) dg = γ(P)^{-1} ∫_{U×M×Ū} f(u m ū) δ_P(m)^{-1} dū dm du`.

Waldspurger states (2) without proof. The integrals in coordinates presuppose two facts.
First, `P = MU` is a topological product decomposition. Second, the product `P Ū` is open in
`G` with coordinates `(p, ū)`. This module proves both facts on rational points. It is a derived
topological adapter: the algebraic content comes from published modules, and this module
transports it to rational points.

- The open immersion `U_G(χ⁻¹) ×_k P_G(χ) → G` is the published
  `Langlands.GroupScheme.oppositeCellStatement` (Conrad–Gabber–Prasad, *Pseudo-reductive
  groups*, 2nd ed., Proposition 2.1.8(3); see `GroupScheme/Absolute/OppositeCellProof.md`).
- The isomorphism `U_G(χ) ×_k Z_G(χ) ≅ P_G(χ)`, `(u, z) ↦ u z`, is the published
  `Langlands.GroupScheme.Dynamic.multiplicationIso` (Conrad, *Reductive group schemes*,
  Theorem 4.1.7(3); see `GroupScheme/Dynamic/SchemeDecomposition.md`).
- Representability of `P_G(χ)`, `Z_G(χ)`, `U_G(χ)` by closed subgroups of affine `G` is the
  published `Dynamic.Affine.isRepresentedBy_*Hom` and `Dynamic.Affine.isClosedSubgroup_*Hom`.
- The topology is the published one. `rationalPointTopology` on
  `RationalPoint k X = (Over.mk (𝟙 (Spec k)) ⟶ X)` is transported from the evaluation
  topology on `RingPoint k X k`. The published point-topology results used are
  `schemePointIsoHomeomorph`, `isOpenEmbedding_schemePointMap`,
  `schemeProductPointHomeomorph` (with `schemeProductPointHomeomorph_symm_apply`),
  `schemePointTopology_eq_affine`,
  `rationalPointSubgroupHomeomorph` and `rationalPoint_isTopologicalGroup`. They implement
  Conrad, *Weil and Grothendieck approaches to adelic points* (2011): Proposition 2.1
  (printed p. 2: the evaluation topology on points of affine schemes, functorial and
  compatible with fiber products) and Proposition 3.1 (printed p. 4: for a local topological
  ring whose units are open with continuous inversion, open immersions give open
  embeddings).

Waldspurger's semi-standard `P = MU` is not identified here with some `P_G(χ) = Z_G(χ) U_G(χ)`.
Nor is `G(F)` identified with `RationalPoint F G.X` carrying `rationalPointTopology F G.X`.
Both identifications belong to the structural interface of the main task.

## Generic results (topological groups)

`G` is a group with a topology for which it is a topological group. `P`, `V`, `M`, `U` are
subgroups with the subspace topology.

- `isOpenEmbedding_openCellMap_of_mul`: let `a : A → G` and `b : B → G` be maps from
  topological spaces with ranges `P` and `V` (`ha : Set.range a = P`,
  `hb : Set.range b = V`), such that `(v, p) ↦ b v * a p` is an open embedding `B × A → G`
  (`hΨ`). Then `openCellMap (p, v) = p v⁻¹` is an open embedding `P × V → G`.
- `isHomeomorph_mul_of_comp`: let `hP'` say that `u m ∈ P` for all `(u, m) ∈ U × M`. Let
  `sU : A → U`, `sZ : B → M`, `sP : C → P` and `Φ : A × B → C` be homeomorphisms (`hsU`,
  `hsZ`, `hsP`, `hΦ`) with `sP (Φ (a, b)) = sU a * sZ b` in `G` (`h`). Then
  `(u, m) ↦ u m` is a homeomorphism `U × M → P`. This result needs no continuity of the
  group operations.
- `isHomeomorph_mul_of_isHomeomorph_mul_swap`: let `hP` and `hP'` say that `m u ∈ P` and
  `u m ∈ P` for all `m ∈ M`, `u ∈ U`. If `(u, m) ↦ u m` is a homeomorphism `U × M → P` (`h`),
  then so is `(m, u) ↦ m u`, because `m u = (u⁻¹ m⁻¹)⁻¹`.

## Results on rational points

Throughout, `k : Type u` is a field with a topology making it a topological ring with open
units (`[IsTopologicalRing k] [IsOpenUnits k]`; Mathlib provides `IsOpenUnits` for a group with
zero with `ContinuousInv₀` and a `T1` topology). The
base is `Spec k`, and `pt = Over.mk (𝟙 (Spec k))`. For a group scheme `G` over `Spec k`,
`(Dynamic.parabolic χ).carrier pt`, `(Dynamic.centralizer χ).carrier pt` and
`(Dynamic.unipotent χ).carrier pt` are the subgroups `P_G(χ)(k)`, `Z_G(χ)(k)` and
`U_G(χ)(k)` of `RationalPoint k G.X`. The cocharacter `χ⁻¹` is
`CommGroupScheme.groupHom (Gm.powerHom (Spec k) (-1)) ≫ χ`.

Products of points:

- `productPointHomeomorph X Y`: `RingPoint k X k × RingPoint k Y k ≃ₜ RingPoint k (X ⊗ Y) k`
  for the scheme-point topologies. It is a convenience wrapper: by definition it is the
  inverse of the published `schemeProductPointHomeomorph k k X Y`
  (`Langlands.AlgebraicGeometry.PointTopology.SchemeProducts`), specialized to coefficient
  ring and value ring `k`. `productPointHomeomorph_apply` says that it sends `(x, y)` to
  `lift x y`. It is the published `schemeProductPointHomeomorph_symm_apply`.
- `rationalPointSchemeHomeomorph X` (for `[IsAffine X.left]`): the published
  `rationalPointEquiv k X` is a homeomorphism from `rationalPointTopology k X` to
  `schemePointTopology k X k`.
- `rationalPointEquiv_eq_comp`: `rationalPointEquiv k X p = (ringTestSelfIso k).hom ≫ p`.
  This uses no topology on `k`.
- `rationalPointProdHomeomorph e` (for `X Y Z` over `Spec k` with affine underlying schemes
  and `e : X ⊗ Y ≅ Z`): the homeomorphism
  `RationalPoint k X × RationalPoint k Y ≃ₜ RationalPoint k Z` for the rational-point
  topologies. `ringTestSelfIso_comp_rationalPointProdHomeomorph` describes its value: after
  precomposition with `(ringTestSelfIso k).hom`, `(x, y)` goes to `lift x y ≫ e.hom`, with
  `x` and `y` precomposed the same way.

The open cell (hypothesis `hι` of `OpenCellIntegration`):

- `isOpenEmbedding_rationalPoint_mul`: let `G`, `U`, `P` be group schemes over `Spec k` with
  affine underlying schemes (`[IsAffine G.X.left] [IsAffine U.X.left] [IsAffine P.X.left]`),
  with homomorphisms `iU : U ⟶ G` and `iP : P ⟶ G`. Assume the underlying morphism of schemes
  of `(fst ≫ iU) * (snd ≫ iP) : U ×_k P → G` is an open immersion (`hm`). Then
  `(x, y) ↦ (x ≫ iU) * (y ≫ iP)` is an open embedding
  `RationalPoint k U.X × RationalPoint k P.X → RationalPoint k G.X`.
- `isOpenEmbedding_openCellMap_rationalPoint` (**the open cell on rational points**): let `G`
  be a group scheme over `Spec k` with smooth structure morphism and affine underlying scheme
  (`[Smooth G.X.hom] [IsAffine G.X.left]`), and let `χ : 𝔾_m ⟶ G` be a cocharacter. Then
  `openCellMap : P_G(χ)(k) × U_G(χ⁻¹)(k) → G(k)`, `(p, v) ↦ p v⁻¹`, is an open embedding for
  `rationalPointTopology k G.X` and the subspace topologies. No connectedness or reductivity
  is assumed.

The Levi decomposition (hypothesis `hhomeo` of `ParabolicHaar`):

- `rationalPointProdHomeomorph_multiplicationIso_comp`: let `G` be a group scheme over `Spec k`
  with separated structure morphism (`[IsSeparated G.X.hom]`), and let `iP`, `iZ`, `iU`
  represent `P_G(χ)`, `Z_G(χ)`, `U_G(χ)` (`hP`, `hZ`, `hU`). Assume `U`, `Z`, `P` have affine
  underlying schemes. Then the homeomorphism `rationalPointProdHomeomorph` of
  `Dynamic.multiplicationIso hP hZ hU` sends `(x, y)` to a point whose composite with `iP` is
  `(x ≫ iU) * (y ≫ iZ)`.
- `isHomeomorph_leviUnipotentMul_of_isRepresentedBy`: let `G` be a group scheme over `Spec k`
  with locally finite type structure morphism and affine underlying scheme
  (`[LocallyOfFiniteType G.X.hom] [IsAffine G.X.left]`). Let `iP`, `iZ`, `iU` represent
  `P_G(χ)`, `Z_G(χ)`, `U_G(χ)` (`hP`, `hZ`, `hU`) and be closed subgroups (`cP`, `cZ`, `cU`).
  Then `(m, u) ↦ m u` is a homeomorphism `Z_G(χ)(k) × U_G(χ)(k) → P_G(χ)(k)` for the subspace
  topologies of `rationalPointTopology k G.X`.
- `isHomeomorph_leviUnipotentMul_rationalPoint` (**the Levi decomposition on rational
  points**): the same conclusion for every group scheme `G` over `Spec k` with
  `[LocallyOfFiniteType G.X.hom] [IsAffine G.X.left]` and every cocharacter `χ`. It uses the
  published closed representatives of `Dynamic.Affine`.
- `isHomeomorph_leviUnipotentCoord_rationalPoint`: under the same hypotheses, with the
  topological group structure `rationalPoint_isTopologicalGroup k G`, the published
  `leviUnipotentCoord` of `ParabolicHaar` for `M = Z_G(χ)(k)`, `U = U_G(χ)(k)` and
  `P = P_G(χ)(k)` is a homeomorphism. This is the hypothesis `hhomeo` of
  `leviUnipotentMeasure_isHaarMeasure` for these subgroups.

The open-cell hypothesis `hnull` of `OpenCellIntegration` is not proved here. It says that
the complement of the open cell is Haar-null.

## Proof notes

- `isOpenEmbedding_openCellMap_of_mul`: `a` and `b` are embeddings, because they are
  restrictions of the open embedding to the slices through the preimages of `1`. Hence they
  are homeomorphisms onto `P` and `V`. Then
  `openCellMap = inv ∘ (fun (v, p) ↦ b v * a p) ∘ e` for the homeomorphism
  `e (p, v) = (b⁻¹ v, a⁻¹ p⁻¹)`.
- `isHomeomorph_mul_of_comp`: the map equals `sP ∘ Φ ∘ (sU⁻¹ × sZ⁻¹)`, a composite of
  homeomorphisms.
- `productPointHomeomorph` and `productPointHomeomorph_apply` reuse the published
  `schemeProductPointHomeomorph` and its inverse formula; this module builds no new product
  construction.
- `isOpenEmbedding_rationalPoint_mul`: under `rationalPointSchemeHomeomorph` and
  `productPointHomeomorph`, the map is postcomposition by the open immersion `m`. That map
  is an open embedding by the published `isOpenEmbedding_schemePointMap`. The identification
  uses `MonObj.comp_mul` and the projection identities of `lift`.
- `isOpenEmbedding_openCellMap_rationalPoint` applies `isOpenEmbedding_openCellMap_of_mul` with
  `a = (· ≫ parabolicHom χ)`, `b = (· ≫ unipotentHom χ⁻¹)`, the published
  representability (whose point equations give the ranges), and the open immersion of
  `oppositeCellStatement`.
- `isHomeomorph_leviUnipotentMul_of_isRepresentedBy`: `rationalPointSubgroupHomeomorph`
  identifies the rational points of `U`, `Z`, `P` with the subgroups. Then
  `rationalPointProdHomeomorph` of `multiplicationIso` and
  `rationalPointProdHomeomorph_multiplicationIso_comp` give the equation needed by
  `isHomeomorph_mul_of_comp` for `(u, z) ↦ u z`. Finally
  `isHomeomorph_mul_of_isHomeomorph_mul_swap` reverses the order. Affineness of `U`, `Z`, `P`
  follows from the closed immersions into affine `G`. Separatedness of `G` follows from
  affineness.
- `isHomeomorph_leviUnipotentCoord_rationalPoint` is the previous theorem, since
  `leviUnipotentCoord` is `(m, u) ↦ ⟨m u, _⟩` by definition.

The group-level steps are kept in the generic lemmas so that the kernel does not unfold the
rational-point homeomorphisms. No heartbeat option is changed.
