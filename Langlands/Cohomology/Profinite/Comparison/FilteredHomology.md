# Homology of a filtered colimit of complexes of modules

`Langlands/Cohomology/Profinite/Comparison/FilteredHomology.lean`, namespace
`Langlands.ProfiniteCohomology`.

General homological algebra used by the comparisons with colimits (`FiniteQuotients.lean`,
`Coefficients.lean`): if a cocone on a filtered diagram of complexes of modules is surjective in
each degree and every element that dies in the cocone point already dies at some later stage, then
its image under the homology functor is a colimit cocone.

## Declarations

- `exists_iCycles_eq`: an element killed by the differential comes from a cycle.
- `shortComplex_homologyπ_eq_zero_iff`, `homologyπ_eq_zero_iff`: a cycle has zero class iff it is
  a boundary.
- `hom_f_d_apply`, `iCycles_d_apply`, `iCycles_cyclesMap_apply`, `homologyMap_homologyπ_apply`:
  elementwise forms of the compatibilities of chain maps with differentials, cycles and classes.
- `cocone_w_apply`: elementwise naturality of a cocone.
- `exists_homologyMap_eq_of_cocone`: under the surjectivity and injectivity hypotheses every class
  of the cocone point comes from a stage; `exists_homologyMap_map_eq_zero_of_cocone`: a class of a
  stage that vanishes in the cocone point vanishes at a later stage.
- `isColimitHomologyMapCocone`: the homology cocone is a colimit.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/FilteredHomology.lean` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names and proofs are
the source's. The Library has the corresponding statements without proofs in
`Langlands/Cohomology/FilteredColimit/Statement.lean`; this file does not use them.

## References

- Standard homological algebra (homology commutes with filtered colimits of modules).
