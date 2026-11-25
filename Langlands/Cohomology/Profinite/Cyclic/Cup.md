# Cup products with a character of a finite cyclic group

`Langlands/Cohomology/Profinite/Cyclic/Cup.lean`, namespace `Langlands.ProfiniteCohomology.GroupCoh`.

For a finite group `G`, a character `χ : G → ℚ/ℤ` gives `δχ ∈ H²(G, ℤ)`; cupping with it gives
`Ĥ⁰(G, A) → H²(G, A)`. When `G` is cyclic and `χ` is injective this is an isomorphism (periodicity),
with an explicit cocycle.

## Declarations

- `isZero_groupCohomology_of_bijective_nsmul`: if multiplication by `|G|` is bijective on `M`,
  then `Hⁿ(G, M) = 0` for `n ≥ 1`; `isZero_groupCohomology_trivial_rat`.
- `h1RatModIntIso`, `h1RatModIntIso_inv_apply`, `isIso_δ_ratSES`, `h1RatModIntIsoH2Int`, `h2IntIsoHom`,
  `h2IntAddEquiv`, `h2IntAddEquiv_symm_apply`, `h2IntAddEquiv_symm_apply_eq_H2_class`:
  `H²(G, ℤ) ≃+ Hom(G, ℚ/ℤ)` for a finite group, and an explicit cocycle for `δχ`.
- `mem_normRangeInvariants_iff`, `tateZeroClass_surjective`: membership in the Library's norm image
  `Langlands.Tate.normImage` and surjectivity of the Library's `Langlands.Tate.zeroClass`.
- `cupRight`, `charClass χ` (`δχ`), `cupCharClassH0`, `cupCharClass A χ : A^G → H²(G, A)` (cup with
  `δχ`).
- `reprIco` and its lemmas, `charCocycle χ` (the cocycle `(g, h) ↦ ⌊χ(g)⌋ + ⌊χ(h)⌋ - ⌊χ(gh)⌋`) and its
  lemmas, `charClass_eq_H2π`, `cupCharClass_apply`, `cupCharClass_apply_charCocycle`: explicit cocycles.
- `normWeight`, `smul_norm_mem_coboundaries₂`, `exists_norm_eq_of_mem_coboundaries₂`,
  `exists_sub_mem_coboundaries₂`, `exists_generator_sum_charCocycle`, `mem_coboundaries₂_of_subsingleton`,
  `cupCharClass_eq_zero_of_mem`, `cupCharClass_eq_zero_iff` (the cup with `δχ` vanishes exactly on
  norms), `cupCharClass_surjective`.
- `tateZeroToH2`, `tateZeroToH2_tateZeroClass`, `tateZeroToH2_bijective`, `tateZeroIsoH2`:
  `Ĥ⁰(G, A) ≅ H²(G, A)` for cyclic `G` and injective `χ`.
- `isCyclic_of_injective_char`, `charComp`, `charKer`, `mem_charKer`, `charBar` and its lemmas,
  `charComp_charBar`: characters through quotients; `invariantsToQuotient`,
  `coe_coe_invariantsToQuotient`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CyclicCupDefs.lean`, `CyclicCup.lean` and
`CyclicCupInflation.lean`, with `h1RatModIntIso` … `h2IntAddEquiv_symm_apply_eq_H2_class` from
`src/GroundTheory/TateCohomology/Characters.lean`, of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Bindings: the source's `cupH` is the Library's
`ordinaryCup` (`Cup/Inflation.lean`); `normRangeInvariants`, `tateCohomologyZeroIso`, `tateZeroClass`
are the Library's `Langlands.Tate.normImage`, `zeroEquiv`, `zeroClass`; the source's
`isZero_groupCohomology_of_bijective_nsmul` (proved there from Tate acyclicity of induced modules) is
proved here from `card_smul_groupCohomology`. The declarations live in the sub-namespace `GroupCoh`
(the source's `GroundTheory.GroupCoh`/`GroundTheory.ProfCoh`), being about finite groups.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §7, Proposition (1.7.1), p. 74 (for a finite cyclic group,
  cup product with a generator of `Ĥ²(G, ℤ)` is an isomorphism `Ĥⁿ(G, A) ≅ Ĥⁿ⁺²(G, A)`);
  `H²(G, ℤ) ≅ Hom(G, ℚ/ℤ)`: §5, p. 52.
- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter VIII,
  §4, Proposition 6, its Corollary and the Remark, pp. 132–133 (the periodicity isomorphisms are the
  cup product with `θ_s = δχ_s`, where `χ_s(s) = 1/n`; `A^G/NA → H²(G, A)` is `a ↦ a.θ_s`).
