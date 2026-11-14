# A simultaneous Galois and torus-unit fixed point

The theorem
`Langlands.Geometry.Building.unramifiedTorusUnitGaloisFixedPoint`
proves the exact published proposition
`Langlands.Geometry.Building.UnramifiedTorusUnitGaloisFixedPointStatement.{u}`.
The universe `u` is arbitrary, and equal and mixed characteristic are both
included. The theorem has no additional premise. The statement and its
imports are unchanged.

For a nonarchimedean local field `F`, a connected reductive `F`-group `G`
and a maximal `F`-split torus `S`, put `K = inertiaFixedField F`. The
conclusion constructs building data `C` for `G_K`, a homomorphism from
`K ≃ₐ[F] K` to permutations of `C.ReducedBuilding`, and a point fixed by
that action and by the character-valuation kernel of `S_K(K)`. The action
is semilinear for the actual coefficient conjugation on `G(K)`.

## Implemented proof

The proof applies
`unramifiedTorusUnitGaloisFixedPoint_of_metricAction` from the paired
finite-orbit reduction to the published theorem
`unramifiedSemilinearMetricAction`. The latter supplies one complete KP
nonpositively curved metric on every supplied full integer-valued building
datum over `K`, with the existing rational-point action isometric and one
coherent semilinear isometric Galois action having finite orbits.

The reduction constructs a suitable datum rather than taking one as a
premise. It extends `S_K` to a maximal `K`-split torus and applies
`quasiSplitIntegerApartmentExistence`. Quasi-splitness follows from
`dimensionLEOneQuasiSplit`, through
`henselianDiscreteQuasiSplit_of_dimensionLEOne` and
`unramifiedQuasiSplit_of_henselianDiscrete`. The valuation, its
surjectivity and its Henselian valuation subring are the published
maximal-unramified constructions. No local-field instance for `K` is used.

The image of an apartment point is fixed by `S(K)^1` by
`torusUnitApartmentFixation`. Coefficient stability of the
character-valuation kernel and semilinearity show that every torus unit
fixes the entire finite Galois orbit of this point. Galois elements
permute the orbit. The complete NPC bounded-set stabilizer theorem
`boundedSetStabilizerFixedPoint`, with geodesics from
`isGeodesicSpace_of_complete_npc`, gives a point fixed by all isometries
preserving that nonempty bounded orbit. It is therefore fixed by both
actions, yielding the exact existential conclusion.

## Provenance and dependency boundary

This is an internal deduction from the named Library theorems. Its source
motivation is the fixed-point step at the start of Kaletha–Prasad
Proposition 9.3.4, printed p.332 / PDF p.363, read with corrected
Section 9.2.1, corrections PDF p.39. The book is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
and the 1 November 2024 corrections as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The original statement and the paired finite-orbit reduction explain the
precise source comparison; this assembly adds no literature assertion.

The implemented finite-orbit stabilizer argument is described above; it
does not reproduce the source's closed-convex-hull construction. No
special torus, Galois-stable apartment, smooth model or bounded-subgroup
fixed-point theorem over `K` is an input. The proof uses none of
`SpecialTorusBoundedModelStatement`, `SpecialTorusIntegralModelStatement`,
`SpecialTorusExistenceStatement`, `UnramifiedSpecialApartmentStatement`
or `ValuationApartmentAxiomsExistenceStatement`, or a theorem depending
on those results.

Worker 214 supplied the original finite-orbit deduction. Worker 255
discharged its quasi-splitness premise and assembled this exact
unconditional proof using the published metric/action theorem.
