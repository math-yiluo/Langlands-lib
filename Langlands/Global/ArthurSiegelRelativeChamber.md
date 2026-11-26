# Relative chamber reduction on all of `G(𝔸_F)` for every compact Iwasawa subgroup

Module `Langlands.Global.ArthurSiegelRelativeChamber`, namespace
`Langlands.Global.AdelicSiegelFactors`. The module proves a relative form of the chamber
reduction of reduction theory: points of the whole adelic group `G(𝔸_F)` (not only of the
norm-one group `G(𝔸_F)¹`) are moved by rational points of a standard parabolic subgroup `P_1`
into a set `N_0(𝔸_F) M_0(𝔸_F)¹ A_T(t) K` whose torus part satisfies the chamber condition for the
simple roots of `P_1` only. The torus is the maximal split torus `T` itself, and `K` is any
compact subgroup with `P_0(𝔸_F) K = G(𝔸_F)`; maximality of `K` is not used. The module contains
no proposition target; it supplies the reduction used by
`Langlands.Global.ArthurTruncation.iwasawaSiegelCovering` (module
`Langlands.Global.ArthurSiegelCoveringProof`).

Throughout, `F` is a number field, `G` a group scheme over `F` (affine, locally of finite
type, connected reductive), `i : T → G` a maximal split torus and `ν` a generic cocharacter;
`P_0 = Standard.parabolicScheme i ν ∅`, `N_0 = Standard.unipotentScheme i ν ∅` and
`M_0 = Standard.leviScheme i ν ∅`, with the adelic maps `ι_N`, `ι_M` of their inclusions. A
standard parabolic subgroup `P_1` is given by a finite set `S₁` of simple relative roots
(`Δ_0^{P_1} = S₁`, `Standard.parabolicHom i ν S₁`).

## Declarations

### `exists_siegelAlgebraicSetup_of_generic`

For connected reductive `G`, a maximal split torus `i` and a generic cocharacter `ν`, there are
`T₀` and `j : T₀ → T` with `IsSiegelAlgebraicSetup F G T i ν T₀ j`. *Proof.* This is the
argument of the published `siegelAlgebraicSetupExistence_of_structural`
(`Langlands.Global.AdelicSiegelSetupExistence`), run for the given `i` and `ν` instead of a
chosen torus: the derived subgroup from `derivedSubgroupRepresentability`, the derived torus
`T₀` from the proof `derivedMaximalSplitTorus`, a split component from
`splitComponentStatement` and its factor through `T`, the product clause from
`derivedCentralSplitTorusProduct`, minimality of `P_0` from `genericMinimalParabolic`, and the
Levi, unipotent, centralizer and root clauses from `standardMinimalLeviStructure`,
`standardLevi_empty_eq_torusCentralizer_of_generic` and
`relativeRoots_torusToStandardParabolic`.

### `exists_torus_iwasawa_factors`

For an actual setup, every compact subgroup `K` with
`IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` and every `g ∈ G(𝔸_F)` there are
`n ∈ N_0(𝔸_F)`, `m ∈ M_0(𝔸_F)¹ = normOneSubgroup F M_0`, an intrinsic positive point
`a ∈ PositiveRealTorus.intrinsicSubgroup F T` and `k ∈ K` with
`ι_N(n) ι_M(m) i(a) k = g`. *Proof.* Write `g = p k` with `p ∈ P_0(𝔸_F)`
(`IsIwasawaCompact.exists_eq`). The Levi retraction `exists_standardLeviPart` splits
`p = ι_N(n) ι_M(m_M)`. The torus `T → M_0` (`torusToStandardLevi`) is maximal split and central
in `M_0` (the setup identifies `M_0` with the centralizer of `T`), hence a split component of
the connected reductive `M_0`, and the surjectivity of
`PositiveRealTorus.splitComponentNormOneDecomposition` writes `m_M` as a positive point of `T`
times a point of `M_0(𝔸_F)¹`. Centrality moves the torus point to the right. These are the
first two steps of the published `IsSiegelAlgebraicSetup.hasMinimalParabolicNormFactors`,
which goes on to pass to the derived torus on norm-one points; here the positive point of `T`
is kept.

### `adelicChainHeightMinimalSet_mul_of_distortionBound`

If `B ≥ 0` is a simultaneous orbit-height distortion bound for a compact set `C`
(`IsSimultaneousOrbitHeightDistortionBound`), `k ∈ C` and `g` lies in the adelic chain
minimal set `adelicChainHeightMinimalSet F G r d ρ v Q c` with `c ≥ 0`, then `k g` lies in
the same set with constant `B² c`. This is the forward direction of the published
`IsSimultaneousOrbitHeightDistortionBound.chainHeightMinimalSet_transport`, for points of
`G(𝔸_F)` instead of `G(𝔸_F)¹`; the proof is the same chain of inequalities.

### `orbitHeight_trivial_mul_rational`

For the trivial representation `MatrixRepresentation.trivial G (Fin n)`, the orbit height of a
vector is invariant under right translation by rational points: the rational matrix is `1`
(`MatrixRepresentation.trivial_affineMatrix`) and `orbitHeight_mul_rational` applies.

### `relativeChainDim`, `relativeChainRep`, `relativeChainIndex`, `relativeChainFamily`, `relativeChainDim_pos`

Auxiliary definitions that prepend one entry to a chain of standard parabolic indices,
representations, dimensions and selected coordinates: at index `0` the index set `S` (later
`S₁`), the trivial representation of dimension `1` and the coordinate `0`; at index `l + 1`
the given data at `l`. `relativeChainDim_pos` records that all dimensions are positive.

### `exists_relativeChamberReduction`

For connected reductive `G`, an actual setup `hS`, a compact `K` with
`IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` and a finite set `S₁` of simple relative
roots, there is `t : ℝ≥0ˣ` such that every `g ∈ G(𝔸_F)` has a rational point `q ∈ G(F)` lying
in the standard parabolic `P_1` (that is, in
`(SubgroupFunctor.range (Standard.parabolicHom i ν S₁)).carrier` at `Spec F`), points
`n ∈ N_0(𝔸_F)`, `m ∈ M_0(𝔸_F)¹`, an intrinsic positive point `a` of `T` with
`t ≤ PositiveRealTorus.normCharacter F T α a` for every `α ∈ S₁`, and `k ∈ K`, such that
`ι_N(n) ι_M(m) i(a) k = q g`.

*Proof.* The argument is that of the published `hasWeakChamberReduction_of_rankOne_height`
(module `Langlands.Global.AdelicChamberFromRankOneHeight`), with three changes: the points are
all of `G(𝔸_F)` and the torus is `T`; only the roots of `S₁` are treated; and the height
minimization runs over `P_1(F)` instead of `G(F)`.

1. Enumerate `S₁` as `α_0, …, α_{r−1}` (`r = |S₁|`). For each `l` let `J_l = Δ_0 ∖ {α_l}`,
   the maximal standard parabolic omitting `α_l`, and take representations `ρ_l` with exact
   Chevalley lines `b_l` for `P_{J_l}` from `exists_adapted_standardParabolicPrefix_minima`.
2. The *relative chain* has `r + 1` entries: at index `0` the parabolic index `S₁` with the
   trivial representation, at index `l + 1` the index `J_l` with `ρ_l` and `b_l`. Its prefix
   subgroups `Q = closedPrefixRationalSubgroup` are intersections of the rational points of the
   preceding parabolics, so `Q 1 = P_1(F)` and `Q (l + 1) ⊆ P_1(F)`.
3. A distortion constant `B` for the compact set `K` and the `r + 1` representations comes
   from `exists_pos_simultaneous_orbitHeight_distortionBound`. Let `S` be the set of points
   `s ∈ T(𝔸_F)` such that `ι_M(m) i(s) ι_N(x)` lies in the adelic chain minimal set with
   constant `B²` for some `m ∈ M_0(𝔸_F)¹` and `x ∈ N_0(𝔸_F)`. For `α_l ∈ S₁` the published
   `hasUniformRootBound_of_minimal_coordinates_and_prefix_minima`, applied at index `l + 1`
   with the proof `rankOneParabolicRationalOrbitHeightBound` of the rank-one arithmetic
   statement, bounds `|α_l|` on `S`. Its hypotheses hold: `α_l ∉ J_l`, and `α_l` lies in every
   preceding index (in `S₁` at index `0`, and in `J_a` for `a < l` because the enumeration is
   injective). That theorem uses the minimum inequality only at index `l + 1` and only for the
   rational points of the root Levi of `α_l`, which lie in the prefix subgroup. Finitely many
   bounds give one bound `C_max`; put `t = C_max⁻¹`.
4. Given `g`, apply `exists_simultaneous_min_orbitHeight` to the entries `1, …, r` of the chain
   with the subgroups `Q (l + 1)`: it gives `q ∈ Q 1 = P_1(F)` such that `g⁻¹ q` minimizes each
   of these heights over `Q (l + 1)`. Later subgroups act on earlier lines by rational
   scalars, because they lie in the corresponding parabolics and the lines are exact
   stabilizer lines (`affine_coordinateLine_scalar_iff`). Together with the trivial entry at
   index `0` (`orbitHeight_trivial_mul_rational`) this places `g⁻¹ q` in the adelic chain
   minimal set with constant `1`.
5. Factor `q⁻¹ g = ι_N(x) ι_M(m) i(a) k` by `exists_torus_iwasawa_factors`. Then
   `(ι_N(x) ι_M(m) i(a))⁻¹ = k (g⁻¹ q)` lies in the minimal set with constant `B²`
   (`adelicChainHeightMinimalSet_mul_of_distortionBound`), and equals
   `ι_M(m⁻¹) i(a⁻¹) ι_N(x⁻¹)` because `i(a)` and `ι_M(m)` commute
   (`IsSiegelAlgebraicSetup.commute_torus_minimalLevi`). So `a⁻¹ ∈ S`, and
   `|α(a⁻¹)| ≤ C_max` gives `t ≤ |α(a)|` for every `α ∈ S₁`. The rational point of the
   conclusion is `q⁻¹ ∈ P_1(F)`.

## Provenance

Derived. The reduction is the height-minimization argument of reduction theory in the form
proved in the Library for Springer's chamber reduction (T. A. Springer, *Reduction theory over
global fields*, 1994, §2.1, statement (F); see the Markdown of
`Langlands.Global.AdelicSiegelChamberReduction` and of
`Langlands.Global.AdelicChamberFromRankOneHeight`). The relative form for `P_1` and the use of
the full torus on all of `G(𝔸_F)` are the forms needed for the covering
`G(𝔸) = P_1(F) S^{P_1}(T_1, ω)` of Arthur, *A trace formula for reductive groups I* (1978),
§6, p.941. All inputs are Library theorems named above; no statement is assumed.
