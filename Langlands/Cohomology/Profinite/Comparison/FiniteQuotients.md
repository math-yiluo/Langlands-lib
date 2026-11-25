# Comparison with the colimit over finite quotients

`Langlands/Cohomology/Profinite/Comparison/FiniteQuotients.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a profinite group `G` and a smooth representation `A`, `Hⁿ(G, A)` is the colimit over the
open normal subgroups `U` of the cohomology `Hⁿ(G/U, A^U)` of the finite quotients, along the
inflation maps. This is Serre's definition; the Library's
`Langlands.Continuous.finiteQuotientCohomology A n` is exactly this colimit. The file builds the
inflation cocone directly on the Library's diagram `finiteQuotientCochainDiagram A` and proves
it is a colimit.

## Declarations

- `isLocallyConstant_comp_quotient_mk`: a function of `(G/U)ⁿ` is locally constant on `Gⁿ`.
- `OpenNormalSubgroup.exists_le_of_finite`: finitely many open normal subgroups contain a common
  one.
- `card_smul_groupCohomology`: for a finite group `Q`, `|Q|` kills `Hⁿ(Q, M)` for `n ≠ 0` (from
  the Library's `Langlands.Tate.PGroupVanishing.card_smul_eq_zero`).
- `transition A h n`: the Library's inflation `finiteInflation A n h : Hⁿ(G/U, A^U) ⟶ Hⁿ(G/V, A^V)`
  for `V ≤ U`.
- `infCochains`, `inflationCochainsX`, `inflationCochains A U`: inflation of cochains from `G/U`
  into the locally constant cochains of `G`; `inflationCochains_f_hom_apply`,
  `inflationCochains_comp_cochainsι`, `inflationCochains_f_injective`.
- `inflation A U n : Hⁿ(G/U, A^U) ⟶ Hⁿ(G, A)`; `inflation_comp_toGroupCohomology` (it is
  Mathlib's inflation followed by the comparison), `transition_comp_inflation`.
- `inflationCochainsCocone A`, `inflationCocone A n`: the cocones on the Library's diagrams.
- `exists_inflationCochains_f_eq`, `inflationCochainsCocone_surj`, `inflationCochainsCocone_inj`:
  every locally constant cochain is inflated from a finite quotient; inflation of cochains is
  injective.
- `exists_inflation_eq`: every class is inflated from a finite quotient;
  `exists_transition_eq_zero`: a class of a finite quotient that inflates to zero dies on a
  smaller quotient.
- `isColimitInflationCocone A n`, and `isoFiniteQuotientCohomology A n : cohomology A n ≅
  Langlands.Continuous.finiteQuotientCohomology A n`, with
  `inflation_comp_isoFiniteQuotientCohomology_hom`: it identifies inflation from `G/U` with the
  Library's structural map `finiteStageToColimit A U n`.
- `exists_card_smul_eq_zero`, `isTorsion_cohomology`: in positive degree `Hⁿ(G, A)` is torsion,
  each class being killed by the order of a finite quotient.

- `subsingleton_cohomology_of_subsingleton_group A hn`: the cohomology of a trivial group vanishes in
  positive degree (from `exists_card_smul_eq_zero`).

Complete type of `subsingleton_cohomology_of_subsingleton_group`, as printed by
`PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.subsingleton_cohomology_of_subsingleton_group.{u} {k H : Type u} [CommRing k] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [Subsingleton H] (A : Rep.{u, u, u} k H) [Langlands.IsSmoothRep A] {n : ℕ}
  (hn : n ≠ 0) : Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology A n)
```

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ColimitDefs.lean` and `Colimit.lean` of the
repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Changed against the source: the source's own diagram
`levelCochains`/`levelFunctor` over `(OpenNormalSubgroup G)ᵒᵖ`, with transition maps built from
`quotientMapOfLE` and `invariantsInclusion`, is replaced by the Library's
`finiteQuotientCochainDiagram`/`finiteQuotientDiagram` over `OrderDual (OpenNormalSubgroup G)`,
with `quotientTransition` and `fixedTransition` (the same maps); so the source's
`cohomologyIsoColimit` becomes `isoFiniteQuotientCohomology`, with no isomorphism of diagrams
needed. The source's `transition` is now an abbreviation of the Library's `finiteInflation`. The
source's use of `GroundTheory.GroupCoh.card_smul_tateCohomology` (its own Tate cohomology) is
bound to the Library's `Langlands.Tate.PGroupVanishing.card_smul_eq_zero`. Source names:
`inflation_comp_cohomologyToGroupCohomology` → `inflation_comp_toGroupCohomology`,
`transitionCochains_comp_inflationCochains` →
`finiteQuotientCochainDiagram_map_comp_inflationCochains`; the others are kept.

`subsingleton_cohomology_of_subsingleton_group` is from
`src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingMackey.lean` of the same repository, with the
source's name.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.2, Proposition 8 and Corollaries 1 and 3, p. 11
  (`H^q(G, A) = lim H^q(G/U, A^U)`; torsion in positive degree). There the cohomology is defined by
  continuous cochains (p. 10); the colimit is the definition in Serre's *Local Fields* (Springer GTM
  67, 1979), chapter X, §3, p. 154.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §2, Proposition (1.2.5), p. 21; torsion: §6, after
  Proposition (1.6.1), p. 60.
