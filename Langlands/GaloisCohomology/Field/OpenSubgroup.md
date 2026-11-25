# Open subgroups of a Galois group and finite subextensions

`Langlands/GaloisCohomology/Field/OpenSubgroup.lean`, namespace `Langlands.GaloisCohomology`.

For a Galois extension `L/K`, the open normal subgroups of `Gal(L/K)` correspond to the finite
Galois subextensions (Krull's theory), and for an open normal subgroup `U` the quotient
`Gal(L/K)/U` is `Gal(L^U/K)`, with `L^U` the invariants of `U` in `L`. These are the finite
levels through which the cohomology of `Gal(L/K)` is computed.

## Declarations

- `isOpen_fixingSubgroup_finiteGalois`, `normal_fixingSubgroup_finiteGalois`,
  `fixingOpenNormalSubgroup E`: the subgroup fixing a finite Galois subextension `E`, as an open
  normal subgroup (`coe_fixingOpenNormalSubgroup`).
- `openNormalToClosed U` (with its normality instance), `fixingSubgroup_fixedField_openNormalSubgroup`,
  instances `finiteDimensional_fixedField_openNormalSubgroup` and
  `isGalois_fixedField_openNormalSubgroup`: the fixed field of an open normal subgroup is a finite
  Galois extension of `K`; `fixedFiniteGalois U` is that subextension
  (`fixedFiniteGalois_toIntermediateField`).
- `quotientEquivGal U : Gal(L/K)/U ≃* Gal(L^U/K)` (`quotientEquivGal_mk_apply`).
- `mem_invariants_additiveModule_iff`, `invariantsAdditiveModuleEquiv U`: the `U`-invariants of
  the additive module are `L^U`, compatibly with the actions of `Gal(L/K)/U` and `Gal(L^U/K)`
  (`invariantsAdditiveModuleEquiv_quotientToInvariants`).
- `fixingOpenNormalSubgroup_fixedFiniteGalois`, `fixedFiniteGalois_fixingOpenNormalSubgroup`,
  `openNormalSubgroupEquiv`: the order-reversing bijection between open normal subgroups and finite
  Galois subextensions (`openNormalSubgroupEquiv_apply`,
  `coe_openNormalSubgroupEquiv_symm_apply`).
- `exists_finiteGalois_le`, `exists_finiteGalois_mem`: every finite subextension, and every
  element of `L`, lies in a finite Galois subextension.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean` of the
repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's, with `galAdd` →
`additiveModule` (`mem_invariants_galAdd_iff` → `mem_invariants_additiveModule_iff`,
`invariantsGalAddEquiv` → `invariantsAdditiveModuleEquiv`, …).

## References

- J. Neukirch, *Algebraic Number Theory* (translated by N. Schappacher, Springer 1999), chapter IV,
  §1, Proposition (1.1), p. 262 (the Krull topology), and Theorem (1.2), p. 263 (the open subgroups
  of `G(Ω|k)` correspond to the finite subextensions).
- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter II, §1.1, p. 71, and chapter I, §1.1, Example 1, p. 3
  (`Gal(L/K)` is the projective limit of the Galois groups of the finite Galois subextensions).
