# Continuous sections of quotients and coinduced modules over a normal subgroup

`Langlands/Cohomology/Profinite/Coinduced/Quotient.lean`, namespace `Langlands.ProfiniteCohomology`.

For a profinite group `G` and a closed normal subgroup `N`, the projection `G → G/N` has a
continuous section. With it, the restriction of a coinduced module to `N` is again coinduced
(from the trivial subgroup of `N`), and its `N`-invariants form the coinduced module of `G/N`;
so both are acyclic. These are the inputs of the inflation–restriction sequences and of Shapiro's
lemma.

## Declarations

- `cosetSelectors`, `univ_mem_cosetSelectors`, `sInter_mem_cosetSelectors`,
  `exists_closed_transversal`: a closed set meeting every coset of `N` in exactly one point
  (Zorn's lemma on closed sets meeting every coset);
  `exists_continuous_section`: a continuous section `G/N → G`.
- `cohomologyIsoOfIso`: isomorphic smooth representations have isomorphic cohomology.
- `sectionRetraction` and its lemmas: the continuous map `G → N`, `x ↦ s(xN)⁻¹ x`.
- `restrictSlice`, `restrictCoindLinear`, `unrestrictCoind`, `resDiscreteCoindIso`: the
  restriction of `discreteCoind k G X` to `N` is `discreteCoind k N (LocallyConstant (G/N) X)`;
  `isZero_cohomology_res_discreteCoind`: hence it is acyclic.
- `apply_eq_of_mem_invariants`, `descendInvariant`, `invariantsDiscreteCoindQuotientEquiv`,
  `quotientToInvariantsDiscreteCoindIso`: the `N`-invariants of `discreteCoind k G X` are
  `discreteCoind k (G/N) X`; `isZero_cohomology_quotientToInvariants_discreteCoind`: acyclic.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/InflationRestriction/Section.lean` and
`InflationRestriction/Coinduced.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §1.2, Proposition 1, p. 4 (continuous sections of `G/K → G/H`
  for closed `K ⊂ H`), and §2.5, pp. 13–14.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §3, Proposition (1.3.6)(ii), p. 31 (an induced `G`-module is
  an induced `H`-module for every closed subgroup `H`, and for normal `H` its `H`-invariants form an
  induced `G/H`-module), and §6, p. 65 (a continuous section of `G → G/H`, by exercise 4 of §1).
