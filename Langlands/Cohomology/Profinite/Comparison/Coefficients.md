# Cohomology of a directed union of subrepresentations

`Langlands/Cohomology/Profinite/Comparison/Coefficients.lean`, namespace
`Langlands.ProfiniteCohomology`.

If a smooth representation `A` of a compact group is the directed union of subrepresentations
`W i` (stable under `G`, monotone in `i`), then `Hⁿ(G, A)` is the colimit of the `Hⁿ(G, W i)`: a
locally constant cochain takes finitely many values, so it takes values in one `W i`.

## Declarations

- `subrepInclusion`, `subrepInclusion_refl`, `subrepInclusion_trans`,
  `subrepInclusion_comp_subtype`: the inclusions `W i ⊆ W j` as morphisms of representations.
- `subrepCochains`, `subrepCochainsCocone`: the diagram of cochain complexes of the `W i` and the
  cocone to the cochains of `A`; `subrepCohomology`, `subrepCohomologyCocone` in degree `n`, with
  `subrepCohomology_map`, `subrepCohomologyCocone_ι_app`.
- `exists_forall_mem_of_isLocallyConstant`: a locally constant map into `A` takes values in some
  `W j`.
- `subrepCochainsCocone_surj`, `subrepCochainsCocone_inj`: the hypotheses of
  `isColimitHomologyMapCocone`.
- `exists_cohomologyMap_subtype_eq`: every class of `A` comes from some `W i`;
  `exists_cohomologyMap_subrepInclusion_eq_zero`: a class of `W i` that vanishes in `A` vanishes
  in some `W j`.
- `isColimitSubrepCohomologyCocone`, `cohomologyIsoColimitSubrep`:
  `Hⁿ(G, A) ≅ colim_i Hⁿ(G, W i)`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ColimitUnion.lean` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the
source's; the coefficient maps are the single `map (.id G)` of `Functoriality.lean` in place of the
source's `cohomologyMap`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §5, Proposition (1.5.1), p. 45 (cohomology commutes with
  direct limits). They state it for a projective system of profinite groups and a direct system of
  modules; here the group is a fixed compact group and the system a directed union of
  subrepresentations.
