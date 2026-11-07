# Overlap conditions for descent of subgroup families

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. A chart's family of tori is built on a
cover `M → B` and then descended to `B` with the Library's descent of closed
subgroups (`Langlands.GroupScheme.Descent`). This module turns the descent
overlap condition into a condition on evaluations, and reduces equality of
evaluations to affine tests of the form `Spec C`. `evaluate j a` is the
Library's `TorusSubgroupModuli.evaluate`: the range of the pullback of the
family `j` along the test point `a`.

## Results

- `baseChange_map_left_fst`: the underlying morphism of the base change of a
  homomorphism `a` commutes with the first projections.
- `hom_ext_triple`: two homomorphisms into an iterated base change
  `r^* p^* qB^* G` are equal if their composites with the three first
  projections down to `G` agree. The proof applies `pullback.hom_ext` three
  times; the second components agree because the structure maps commute.
- `overlap_range_eq_of_evaluate_eq`: let `p : M.left → B` and `qB : B → S₀`
  with `p ≫ qB = M.hom`, and let `j` be a family of subgroups over `M`. Suppose
  that `evaluate j a = evaluate j b` for every two test points `a` and `b` of
  `M` with `a ≫ p = b ≫ p`. Then the two pullbacks of `j` (transported along
  `pullbackComparison`) to the overlap `M ×_B M` have the same range after the
  canonical identification `canonicalOverlap`. This is the hypothesis of the
  Library's descent of closed subgroups. Proof: apply the hypothesis to the two
  projections `fst p` and `snd p` of the overlap, viewed as test points. Both
  pullbacks then factor as `familyHom j (fst p)` and `familyHom j (snd p)`
  followed by one isomorphism `Ψ`. Identifying the second factorization uses
  `hom_ext_triple`, and `SubgroupFunctor.range_comp_iso_eq_iff` concludes.
- `evaluate_eq_of_specOver`: let `j` be a closed family over `M` over
  `Spec R`, and `Φ` a relation on pairs of test points that is stable under
  precomposition. Suppose `Φ a b` implies `evaluate j a = evaluate j b`
  whenever the test object is `FiniteSource.specOver R C` for an `R`-algebra
  `C` in universe `u`. Then the implication holds for every test object `T`.
  Proof: equality of evaluations of closed families is local on the affine
  cover of `T` (`evaluate_eq_iff_openCover`). Each member is isomorphic over
  `Spec R` to `specOver R Γ(T', ⊤)`, and `evaluate_eq_comp` transports along
  this isomorphism.
