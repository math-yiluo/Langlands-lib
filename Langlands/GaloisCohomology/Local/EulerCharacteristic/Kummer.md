# Kummer theory over open subgroups and conjugation

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Kummer.lean`, namespaces `Langlands.ProfiniteCohomology` (any profinite group) and `Langlands.GaloisCohomology` (fields).

For open subgroups `V ≤ U` of `Gal(Ksep/K)` with `V` normal in `U` and fixed fields `F ⊇ E`, the
groups `Hⁱ(V, μ_l)` (`i ≤ 2`) are described with the action of `U/V = Gal(F/E)` by conjugation:
`H⁰(V, μ_l) = μ_l(F)`, `H¹(V, μ_l) ≅ Fˣ/Fˣˡ` (Kummer) and `H²(V, μ_l) ≅ ℤ/l` with trivial action
(through the local class formation). These are the inputs of the coprime case.

## Declarations

- `zeroIso_hom_cohomologyMapAlong` (through `zeroIso_hom_cohomology_class_zero` of
  `Langlands.Cohomology.Profinite.Duality.DualModule`), `invariantsConj`,
  `zeroIso_hom_cohomologyConj`, `cohomologyConj_zeroIso_inv`, `δ_zeroIso_inv_invariantsConj`.
- `cohomologyRes_subgroupOf_surjective`, `ClassFormation.cohomologyConj_two_eq_id`.
- `kummerSequenceResRes` and its smoothness instances, `kummerSequenceResRes_shortExact`,
  `subsingleton_cohomology_one_galUnits_subgroupOf`, `cohomologyConj_two_galRootsOfUnity_eq_id`.
- `fixedFieldConj`, `fixedFieldConjHom` (the action of `U` on `F`), `unitOfMemFixedField`,
  `unitsInvariantsOpenEquiv`, `rootsInvariantsOpenEquiv`, `cohomologyZeroRootsEquiv`.
- `kummerOpenHom` (Kummer map `Fˣ → H¹(V, μ_l)`), `kummerOpenHom_surjective`,
  `kummerOpenHom_eq_zero_iff`, `kummerOpenModNHom_bijective`, `cohomologyOneRootsEquiv`,
  `kummerOpenHom_smul`, `cohomologyOneRootsEquiv_cohomologyConj`.
- `fixedFieldGalHom`, `quotientFixedFieldGalEquiv : U/V ≃ Gal(F/E)`,
  `cohomologyZeroRootsEquiv_cohomologyConj_gal`, `cohomologyOneRootsEquiv_cohomologyConj_gal`.
- `rootsOfUnityTwoInv`, `rootsOfUnityTwoEquivOpen`, `cohomologyTwoRootsEquiv`,
  `cohomologyTwoRootsEquiv_cohomologyConj`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/SubsingletonCohomologyOneGalUnitsSubgroupOf.lean`,
`H0IsoHomCohomologyClassZero.lean`, `CohomologyKummer.lean`, `CohomologyGal.lean` and
`Cohomology.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The class formation used for `H²` is `Local.classFormation`
(`ClassFormation.lean`), on the Library's invariant.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
