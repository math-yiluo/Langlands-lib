# A finite-orbit reduction to a simultaneous fixed point

This module proves the exact published
`UnramifiedTorusUnitGaloisFixedPointStatement.{u}` conditionally on
`UnramifiedSemilinearMetricActionStatement.{u}`. That premise is explicit
in this reduction. The separate module
`UnramifiedTorusUnitGaloisFixedPointProof` discharges it with the published
`unramifiedSemilinearMetricAction` and proves the unconditional target.

Worker 214 wrote the two original finite-orbit theorems in Task 6196 draft
revision 3. Worker 255 checked the interfaces and added the
`unramifiedTorusUnitGaloisFixedPoint_of_metricAction` composition, which
discharges the original quasi-splitness premise using published results.

## Implemented argument

`exists_commonFixedPoint_of_finiteOrbit` works for any metric space `Y` in an
independent universe `v`, equipped with the actual rational-point action over
`K = inertiaFixedField F`. It assumes a complete KP nonpositively curved
metric, isometry of the rational-point action, a coherent semilinear Galois
action by isometries, and a point `x` fixed by the character-valuation kernel
of the scalar-extended source `S`. Only the Galois orbit of `x` is required
to be finite; this helper needs no reductivity or splitness of `S` or `G`.

Let `O` be this finite orbit. It is nonempty and bounded. For a source unit
`t` and a coefficient automorphism `sigma`, conjugate `t` by `sigma` inverse.
The published `rationalConjugate_mem_characterValuationKernel_iff` and
`MaximalUnramified.valuation_galois` show that the resulting point is still a
source unit. Fixation at `x`, naturality of coefficient conjugation and
semilinearity show that `t` fixes `rho sigma x`. Thus each source unit fixes
`O` pointwise, while the homomorphism law for `rho` shows that Galois elements
permute `O`.

The published `boundedSetStabilizerFixedPoint`, using geodesics obtained from
`isGeodesicSpace_of_complete_npc`, gives a single point fixed by every
isometry preserving `O`. Apply it first to each coefficient permutation and
then to the isometry defined by each source unit. The result is fixed by both
actions.

`unramifiedTorusUnitGaloisFixedPoint_of_semilinearMetricAction` first extends
the given split subtorus `S_K` to a maximal `K`-split torus using
`exists_maximalSplitTorus_extension`. Under its quasi-splitness premise,
`quasiSplitIntegerApartmentExistence` gives full integer-valued apartment
data adapted to that torus. This uses the published surjectivity of the
integer-normalized valuation and Henselianity of its valuation subring.
`connectedReductiveFieldExtensionStatement` supplies reductivity after base
change. The constructed `C` is an actual `MaximalUnramified.BuildingData`.

The metric/action premise supplies the complete NPC metric, the existing
rational-point action's isometry, and the coherent semilinear isometric Galois
action with finite orbits on `C.ReducedBuilding`. Pick a point of its nonempty
apartment. The split-subtorus factorization and published
`torusUnitApartmentFixation` make its apartment image fixed by `S(K)^1`.
The first theorem then gives the required simultaneous fixed point. The
building datum, homomorphism and point are all existential conclusions.

Finally, `unramifiedTorusUnitGaloisFixedPoint_of_metricAction` removes the
quasi-splitness premise by the literal published composition

```lean
unramifiedQuasiSplit_of_henselianDiscrete
  (henselianDiscreteQuasiSplit_of_dimensionLEOne dimensionLEOneQuasiSplit)
```

The dimension-one theorem has no additional premise. The Henselian discrete
reduction uses exactly the valuation, Henselian valuation-subring and actual
algebraically closed residue hypotheses; the unramified reduction supplies
them for the actual `K`. No assertion that `K` is a local field is used.
The final conditional theorem is universe-polymorphic in `u` and covers both
characteristics. The metric/action premise remains an explicit argument.

## Provenance and dependency boundary

This is an internal deduction from the named Library results and the
explicit metric/action premise. Its motivation is the opening fixed-point
step of KP Proposition 9.3.4, printed p.332 / PDF p.363, read with the
replacement finite-orbit paragraph and added fixed-point paragraph of
corrected Section 9.2.1, corrections PDF p.39. The argument uses the finite
orbit of an apartment point in the supplied invariant metric. It does not
assume a globally Galois-stable apartment or construct a special F-torus.

The registered book is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered 1 November 2024 corrections are
`kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The implemented proof route is the deduction above, rather than a claim
that KP use these exact Library interfaces. No special-torus theorem,
valuation-apartment existence theorem, bounded-subgroup theorem over `K`,
or smooth model is a proof input. The metric and coherent Galois action are
supplied by the explicit premise, whose published proof is imported only by
the separate unconditional assembly.
