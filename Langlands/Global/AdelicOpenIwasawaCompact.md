# A compact subgroup, an open subgroup and finitely many translates for the Siegel setup

Author: Worker 3994. Part of task 40747bb3 (finite volume of `G(F) \ G(𝔸_F)¹`).

The published route to Siegel finite volume needs a compact subgroup `K` of `G(𝔸_F)` with
`P(𝔸_F) K = G(𝔸_F)`. At the finite places this requires an Iwasawa decomposition. This
module builds a weaker substitute that uses only the Iwasawa decomposition at the infinite
places:

- a compact subgroup `K`;
- an open subgroup `H₁ ⊇ K` with `H₁ ⊆ P(𝔸_F) K`;
- a finite set `W ⊆ G(𝔸_F)¹` with `P(𝔸_F) K W = G(𝔸_F)`.

The construction is internal supporting material for
`Langlands/Global/AdelicFiniteVolumeProof.lean`. It has no single literature source. It
combines the archimedean Iwasawa decomposition (Getz–Hahn, Theorem B.4.1, printed p.547;
Theorem B.1.1, p.541 supplies the good-position context), the existence of a compact
open subgroup of `G(𝔸_f)`, and the compactness of `P(𝔸_F) \ G(𝔸_F)¹` in the form of a
compact norm-one parabolic cover. All three are already in the Library.

## Notation

- `F` is a number field and `G` an affine group scheme over `Spec F`.
- `G(𝔸_F) = AdelicGroupPoints F G`.
- `AdelicGroupPoints.split F G` is the Library homeomorphic isomorphism
  `G(𝔸_F) ≅ G(𝔸_∞) × G(𝔸_f)`. Its components are `infinite F G` and `finite F G`.
- `InfiniteAdelicGroupPoints.completions F G` identifies `G(𝔸_∞)` with `∏_w G(F_w)` over the
  infinite places `w`.
- `atInfinitePlace F G w : G(𝔸_F) → G(F_w)` is the component at `w`.

## Declarations

- `AdelicGroupPoints.atInfinitePlace_eq_atPlace_infinite`: the `w`-component of an adelic
  point equals the `w`-component of its infinite part:
  `atInfinitePlace F G w g = InfiniteAdelicGroupPoints.atPlace F G w (infinite F G g)`.
  Both sides are compared through the injective coordinate evaluation
  `affinePointEvaluation`. The left projection `𝔸_F → 𝔸_∞` followed by `𝔸_∞ → F_w` is the
  projection `𝔸_F → F_w`.
- `AdelicGroupPoints.finite_map`: for a homomorphism of affine group schemes `f : G → H`,
  taking the finite adelic part commutes with the adelic map of `f`:
  `finite F H (map F G H f g) = G.affinePointsTarget f _ (finite F G g)`. This is the
  naturality of `affinePointsTarget` for the projection `𝔸_F → 𝔸_f`.
- `AdelicSiegelFactors.exists_compact_openSubgroup_finite_cover` (main result). Let `G` be
  locally of finite type and connected reductive. Let `T, i, ν, T₀, j` be data with
  `IsSiegelAlgebraicSetup F G T i ν T₀ j`, and let `P = Standard.parabolicScheme i ν ∅` be
  the canonical minimal parabolic, with adelic image `P(𝔸_F)` (the range of the adelic map
  of `Standard.parabolicHom i ν ∅`). Then there are subgroups `K` and `H₁` of `G(𝔸_F)` and a
  set `W ⊆ G(𝔸_F)` such that:
  1. `K` is compact;
  2. `H₁` is open;
  3. `K ≤ H₁`;
  4. `H₁ ⊆ P(𝔸_F) K`;
  5. `IsPositiveTorusCompatible F G T i ν T₀ j K`: every element of `K ∩ P(𝔸_F)` commutes
     with the positive torus `A_{T₀}`;
  6. `W` is finite;
  7. `W ⊆ G(𝔸_F)¹`;
  8. `P(𝔸_F) (K W) = G(𝔸_F)`.

## Proof of the main result

1. **Local data.**
   - The Library theorem `InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement` gives,
     for every infinite place `w`, a subgroup `K_w ≤ G(F_w)` satisfying
     `IsLeviCompatibleIwasawaCompact` for `P` and its Levi
     `Standard.leviScheme i ν ∅`. In particular `K_w` is maximal compact, hence compact,
     and `P(F_w) K_w = G(F_w)`.
   - `U = FiniteAdelicGroupPoints.compactOpenSubgroup F G` is a compact open subgroup of
     `G(𝔸_f)`.
2. **The subgroups.**
   - `K` is the preimage under `split` of `(completions⁻¹ ∏_w K_w) × U`. So `g ∈ K` if and
     only if `g_w ∈ K_w` for every infinite place `w` and `finite g ∈ U`. This uses
     `atInfinitePlace_eq_atPlace_infinite`.
   - `H₁` is the preimage of `U` under `finite`.
3. **Properties 1–3.**
   - `K` is compact: a finite product of compact groups is compact (`isCompact_univ_pi`),
     the product with the compact `U` is compact, and `split` and `completions` are
     homeomorphisms.
   - `H₁` is open because `U` is open and `finite` is continuous.
   - `K ≤ H₁` is immediate from the description of `K`.
4. **Property 4, `H₁ ⊆ P(𝔸_F) K`.** Let `g ∈ H₁`.
   - For each infinite place `w`, write `g_w = p_w k_w` with `p_w ∈ P(F_w)` and
     `k_w ∈ K_w`, using the archimedean Iwasawa decomposition.
   - Let `x ∈ P(𝔸_F)` be the point with infinite part
     `InfiniteAdelicGroupPoints.assemble F P (p_w)_w` and trivial finite part
     (`ofInfinite`). Write `x` also for its image in `G(𝔸_F)`.
   - Then `g = x (x⁻¹ g)`. The `w`-component of `x⁻¹ g` is `p_w⁻¹ g_w = k_w ∈ K_w`, by
     `atPlace_map` and `atPlace_assemble`.
   - The finite part of `x⁻¹ g` is `finite g ∈ U`, because the finite part of `x` is `1`
     (`finite_map`, `finite_ofInfinite`). Hence `x⁻¹ g ∈ K`.
5. **Property 5.** The published
   `isPositiveTorusCompatible_of_setup_leviCompatibleIwasawaCompacts` needs only that every
   archimedean component of every element of `K` lies in the corresponding `K_w`, which holds
   by construction.
6. **Properties 6–8.**
   - `IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover` gives a compact
     `Ω₀ ⊆ G(𝔸_F)¹` with `P(𝔸_F) Ω₀ = G(𝔸_F)`.
   - The right translates `H₁ x`, for `x ∈ Ω₀`, are open and cover `Ω₀`. By compactness
     (`IsCompact.elim_finite_subcover_image`), a finite set `W ⊆ Ω₀` already has
     `Ω₀ ⊆ ⋃_{w ∈ W} H₁ w`. Then `W` is finite and `W ⊆ Ω₀ ⊆ G(𝔸_F)¹`.
   - For any `g`, write `g = y z` with `y ∈ P(𝔸_F)` and `z ∈ Ω₀`. Then `z = h w` with
     `h ∈ H₁` and `w ∈ W`, and `h = y' k` with `y' ∈ P(𝔸_F)` and `k ∈ K` by property 4.
     So `g = (y y') (k w) ∈ P(𝔸_F) (K W)`.
