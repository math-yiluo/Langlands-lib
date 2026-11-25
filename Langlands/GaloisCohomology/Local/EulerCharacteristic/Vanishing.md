# Vanishing of cohomology under nontrivial tame inertia

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Vanishing.lean`, namespace `Langlands.GaloisCohomology.Local`.

Let `l ≠ p` be a prime, `V ≤ W` open subgroups of `Gal(Ksep/K)` with `V` normal in `W` of index
prime to `l`, `μ_l` contained in the fixed field `E` of `V`, and `W` acting on `E` through inertia
(`v(gx − x) < 1` for integral `x`). For a finite `l`-torsion module `M` on which `V` acts trivially
and `W` has no nonzero fixed points, `Hⁱ(M) = 0` for `i ≤ 2` (`subsingleton_cohomology_of_inertia`).
Conjugation by `W` acts trivially on `Hⁱ(V, μ_l)` (in degree one by Kummer theory and
`exists_map_units_eq_mul_pow`), and `M` is a sum of copies of `μ_l` up to the index. The
valuative relation of `Ksep` is a hypothesis; fixed fields carry the restricted relation and the
topology of the Library's spectral norm.

## Declarations

- `fixedFieldTopology K V` (the spectral norm topology on a fixed field),
  `isNonarchimedeanLocalField_fixedField`, `valuation_le_valuation_iff_coe`,
  `valuation_le_one_iff_coe`, `valuation_lt_one_iff_coe`, `valuation_eq_iff_coe`,
  `natCast_residueField_fixedField_ne_zero`, `natCast_ne_zero_of_residueField`.
- `cohomologyConj_zero_eq_id_of_apply`, `apply_eq_of_valuation_sub_lt_one`,
  `cohomologyConj_one_galRootsOfUnity_eq_id`, `cohomologyConj_galRootsOfUnity_eq_id`.
- `addHomToULiftLinear`, `exists_sum_addHom_comp_eq`.
- `subsingleton_cohomology_of_inertia_open`, `subsingleton_cohomology_of_inertia`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Vanishing.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source's
`finiteExtensionStructure` is the Library's `LocalField.FiniteExtension` (`fixedFieldTopology`,
`valuativeRel_eq_spectral` of `Arithmetic/SeparableClosure.lean`); intermediate-field instances are
the scoped ones of that file.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
