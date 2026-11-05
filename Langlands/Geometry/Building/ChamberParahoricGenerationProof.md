# Generation by the actual chamber parahoric and zero normalizer

Authors: Worker 1671 and Worker 1632.

`chamberParahoricGeneration` proves exactly the published proposition
`ChamberParahoricGenerationStatement.{u}`. The universe `u` is arbitrary.
For every nonarchimedean local field `F`, affine group scheme `G`, actual
`P : ParahoricBuildingData G` satisfying
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, and actual chamber `C`,
the conclusion is

```
P.zeroSubgroup ≤ P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup).
```

The target statement, its Markdown, and their imported modules are unchanged.
The proof uses the actual group schemes, lattices, all-test dynamic subgroup
functors, root groups, normalizer, and zero subgroup already defined in the
Library. It adds no structural, splitness, characteristic, or field hypothesis.

The implemented proof combines four supporting modules:

1. `ChamberRootGeneration` puts every actual root group into the desired join.
   A positive derived cocharacter has a positive power whose evaluated values
   lift to the actual simply connected cover. These values lie in
   `N(F) ∩ G(F)^0`. Their conjugations contract a root-group point into the
   chamber root fixer, which lies in the parahoric; conjugating back proves
   root containment.
2. `ApartmentRootRays` derives disjointness of distinct indivisible root rays
   from the supplied apartment's affine coroots and integral cross-pairings.
   It proves a consequence for this actual apartment, without assuming a
   global relative-root-system or rank-one factorization proposition.
3. `DynamicRadicalRootGeneration` uses that local ray-disjointness together
   with the proved semigroup realization, ordered unipotent products, and
   dynamic and cyclic-root comparisons. Thus every complete dynamic radical
   of a torus cocharacter lies in the join.
4. `ChamberGenerationOpenCell` uses the proved Zariski density of rational
   points over the local field and the proved opposite open cell. Two cell
   points whose ratio is `g ∈ G(F)^0` have radical factors in the join.
   Removing those factors leaves a whole-torus centralizer element which
   also lies in `G(F)^0`, hence in `N(F) ∩ G(F)^0`. This proves the displayed
   generation inclusion.

The final Lean theorem applies the fourth module's reduction, supplies complete
radical containment from the third module, and discharges its two premises
with the second and first modules. The argument retains the actual zero
subgroup intersection throughout. Empty root sets are handled by the same
finite products.

The proof route is an internal derivation from existing Library results and
the four supporting constructions. It does not assume the unproved global
`RationalBruhatStatement` or `DynamicRootOrderedProductStatement`, and it does
not use a relative or affine Tits system as an input.
