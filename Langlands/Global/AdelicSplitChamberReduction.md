# Chamber reduction from root-Levi height bounds, and its split case

Author: Worker 5253.

This internal derived module reruns the published chamber reduction
`hasWeakChamberReduction_of_rankOne_height` (`AdelicChamberFromRankOneHeight`) with a
weaker arithmetic premise. That proof uses the universal rank-one statement
`RankOneParabolicRationalOrbitHeightBoundStatement` only through
`hasUniformNormOneRationalOrbitHeightBound_rootLevi`
(`AdelicRootLeviHeightNormalization`). That theorem applies the rank-one statement
to the singleton standard Levis `L_α` of one fixed setup. Here this input is isolated
as a hypothesis on the fixed setup, `HasRootLeviHeightBounds`. For split groups it
then follows from the published split rank-one statement
`SplitRankOneParabolicRationalOrbitHeightBoundStatement`.

The module proves no unconditional result. The split rank-one statement remains an
explicit hypothesis.

## The definition

Fix a number field `F`, an affine group scheme `G` over `F`, a torus `T` with
`i : T → G`, and a cocharacter `ν` of `T`. For a set `J` of characters, write `P_J`
for `standardParabolic i ν J`, `L_J` for `Standard.leviScheme i ν J` and
`ι_{L_J}` for `Standard.leviHom i ν J`.

`HasRootLeviHeightBounds F G T i ν` is the proposition: for every simple relative
root `α ∈ simpleRelativeRoots i ν`, every set `K ⊆ simpleRelativeRoots i ν` with
`α ∉ K`, every finite-coordinate representation `ρ : G → GL_n` and every coordinate
index `b` such that the exact stabilizer of the coordinate line `b` is `P_K`
(`ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν K) b`), the restricted
representation `ρ ∘ ι_{L_{α}}` has a uniform norm-one rational-orbit height bound
at the basis vector `e_b` on `L_{α}`. That is,
`HasUniformNormOneRationalOrbitHeightBound F (Standard.leviScheme i ν {α})
(ρ.restrict (Standard.leviHom i ν {α})) (Pi.single b 1)`.

### Provenance

This is a **derived** internal hypothesis, not a statement of the source. In
Springer, *Reduction theory over global fields* (1994), the proof of the fundamental
set property (F) (§§2.3–2.4 and §§3.2–3.3) reduces general groups to semisimple rank
one. In Springer's notation (§2.3, p.212) `P_H` is the standard parabolic whose Levi
root system has basis `H ⊆ Δ`. The group `L_{α}` used here is therefore the Levi of
the standard parabolic `P_{α}` with the **singleton** index `H = {α}`. It has
semisimple rank one. It is not the Levi of a maximal standard parabolic: those are
indexed by `H = Δ \ {α}` (§2.5, p.213) and have Levi root systems of rank `|Δ| - 1`.

The two kinds of parabolic play different roles in the chamber argument. The
eigenlines are chosen for the maximal standard parabolics: in the Library's chamber
reduction, `ρ` has an exact line stabilizer `P_K` with `K = Δ \ {α}`. The
representation `ρ` is then restricted to the singleton-index Levi `L_{α}`, and the
height bound is used for that restriction. `HasRootLeviHeightBounds` allows any
`K` with `α ∉ K`, which includes `K = Δ \ {α}`.

`HasRootLeviHeightBounds` records exactly the rank-one information that the
Library's chamber reduction consumes: the conclusion of
`hasUniformNormOneRationalOrbitHeightBound_rootLevi`, for one fixed setup. Its
hypotheses are those of that published theorem; only the rank-one premise is
removed.

## Theorems

`hasRootLeviHeightBounds_of_rankOne`: for `G` connected reductive of locally finite
type, `i` maximal split and `ν` generic, the universal rank-one statement gives
`HasRootLeviHeightBounds F G T i ν`. The proof is the published
`hasUniformNormOneRationalOrbitHeightBound_rootLevi`.

`hasRootLeviHeightBounds_of_splitRankOne`: under the same hypotheses together with
`IsMaximalTorus i` (so `G` is split), the split rank-one statement already gives
`HasRootLeviHeightBounds F G T i ν`. The proof checks each hypothesis of the split
statement for `L = L_{α}` with its torus factor
`iL = standardLeviTorusFactor i ν {α} _`:

- `L` is connected reductive: `standardLeviSplitComponentStatement`.
- `L` is of locally finite type: `ι_L` is a closed immersion
  (`Standard.isClosedSubgroup_leviHom`) and `G` is of locally finite type.
- `iL` is maximal split: `isMaximalSplitTorus_standardLeviTorusFactor`.
- `iL` is a maximal torus: `iL ≫ ι_L = i` (`standardLeviTorusFactor_comp`), `i` is a
  maximal torus of `G`, and `ι_L` is a closed immersion, so
  `IsMaximalTorus.of_comp` applies.
- `ν` is generic for `iL` and `simpleRelativeRoots iL ν = {α}`:
  `standardLeviStandardFamilies`.
- The exact stabilizer in `L` of the line `b` for `ρ ∘ ι_L` is the standard parabolic
  of `L` for `{α} ∩ K = ∅`: `standardLevi_inter_coordinateLine_stabilizer`.

The split statement then gives the bound.

`exists_bounded_rootLevi_normalization_of_prefix_minima_of_rootLevi` and
`hasUniformRootBound_of_minimal_coordinates_and_prefix_minima_of_rootLevi` copy the
published `exists_bounded_rootLevi_normalization_of_prefix_minima`
(`AdelicRootLeviHeightNormalization`) and
`hasUniformRootBound_of_minimal_coordinates_and_prefix_minima`
(`AdelicRootLeviTorusBound`) with the same statements, except that the hypothesis
`HasRootLeviHeightBounds F G T i ν` replaces the universal rank-one statement. Their
proofs are the published proofs. The only change is that the root-Levi height bound
comes from the hypothesis `hroot` instead of from
`hasUniformNormOneRationalOrbitHeightBound_rootLevi`.

`AdelicSiegelFactors.hasWeakChamberReduction_of_rootLeviHeightBounds`: for `G`
connected reductive of locally finite type, an actual algebraic Siegel setup
`IsSiegelAlgebraicSetup F G T i ν T₀ j`, the root-Levi input and a parabolic Iwasawa
compact subgroup `K` for the minimal parabolic, `HasWeakChamberReduction F G T i ν T₀
j K` holds. The proof is the published proof of
`hasWeakChamberReduction_of_rankOne_height`, with the two copied lemmas above in
place of their published versions. In outline: enumerate the simple relative roots;
take exact Chevalley eigenlines of the maximal standard parabolics with simultaneous
rational minima; transfer minima through the compact factor; bound each simple root on
the torus points of minimal products; and invert the Iwasawa factorization of
`q⁻¹ g`.

`AdelicSiegelFactors.hasWeakChamberReduction_of_splitRankOne_height`: for a split
setup (`IsMaximalTorus i`), the split rank-one statement gives the weak chamber
reduction for every parabolic Iwasawa compact subgroup `K`. It combines the two
previous results.
