# The invariant of a local field on `H²(Gal(Ksep/K), Ksepˣ)`

`Langlands/GaloisCohomology/Local/Invariant.lean`, namespaces `Langlands.GaloisCohomology` (open
subgroups and restriction, for any field) and `Langlands.GaloisCohomology.Local` (local fields).

For a nonarchimedean local field `K` (Mathlib's `IsNonarchimedeanLocalField`) and a separable
closure `Ksep`, the invariant `H²(Gal(Ksep/K), Ksepˣ) ≃ ℚ/ℤ` in the cochain model of
`Langlands.ProfiniteCohomology` is the Library's Brauer invariant `localBrauerInvariant K` read
through `Br(K) ≅ H²(Gal(Ksep/K), Ksepˣ)` (`brauerEquiv`). It is normalized by the arithmetic
Frobenius, as the Library's invariant is. Restriction to a finite extension multiplies it by the
degree. For an open subgroup `U` of `Gal(Ksep/K)` the invariant of the fixed field of `U` gives an
invariant on `H²(U, Ksepˣ)`, compatible with restriction up to the relative index.

## Declarations

Open subgroups and fixed fields (`K`, `Ksep` any fields, `Ksep/K` Galois):

- Instance `isSepClosure_intermediateField`: a separable closure of `K` is a separable closure of
  every intermediate field.
- `fixingSubgroup_fixedField_openSubgroup U`: the fixing subgroup of the fixed field of an open
  subgroup `U` is `U`; instances: the fixed field is finite over `K`
  (`finiteDimensional_fixedField_openSubgroup`) and `Ksep` is Galois over it
  (`isGalois_fixedField_openSubgroup`).
- `index_openSubgroup U`: the index of `U` is the degree of its fixed field;
  `fixedField_le_fixedField`: `V ≤ U` gives the inclusion of fixed fields the other way;
  `relIndex_eq_finrank h`: for `V ≤ U` the relative index is the degree of the fixed field of `V`
  over that of `U`.
- `galFixedFieldToOpen U`, `galFixedFieldEquivOpen U`: `Gal(Ksep/Ksep^U) ≅ U` (restriction of
  scalars), continuous with continuous inverse (`continuous_galFixedFieldEquivOpen`,
  `continuous_galFixedFieldEquivOpen_symm`), bundled as `galFixedFieldHomOpen U`;
  `coe_galFixedFieldToOpen_apply`, `galFixedFieldToOpen_bijective`,
  `galFixedFieldEquivOpen_toMonoidHom`.
- `unitsModuleOpenHom U` (the identity of `Ksepˣ` as a morphism from the units module of `K`
  restricted to `U` to the units module of `Ksep^U`, bijective by
  `unitsModuleOpenHom_bijective`) and `openCohomologyIso U n : Hⁿ(U, Ksepˣ) ≅ Hⁿ(Gal(Ksep/Ksep^U),
  Ksepˣ)` (`openCohomologyIso_hom`).
- `isZero_cohomology_one_res_unitsModule U`: Hilbert 90, `H¹(U, Ksepˣ) = 0`, for every open
  subgroup.

Restriction along an extension `F/E` inside `L` (`L` Galois over both):

- `unitsRestriction E F L n : Hⁿ(Gal(L/E), Lˣ) → Hⁿ(Gal(L/F), Lˣ)`: the map of the Library's
  `continuousUnitRestriction E F L L` in the cochain model;
  `unitsModuleContinuousEquiv_unitsRestriction` (the comparison with the Library's continuous
  cohomology), `krullRestriction_self_apply` (the restriction homomorphism acts as `σ` on `L`).
- `unitsRestriction_brauerEquiv a`: for separable closures, restriction of `brauerEquiv E L a` is
  `brauerEquiv F L` of the scalar extension of `a` to `F`.

Local fields:

- `invariant K Ksep : H²(Gal(Ksep/K), Ksepˣ) ≃+ ℚ/ℤ`, with `invariant_brauerEquiv` (its value on
  `brauerEquiv K Ksep x` is `localBrauerInvariant K x`) and `invariant_symm_apply`.
- `invariant_unitsRestriction hcont x`: for a finite extension `L` of local fields
  (`ValuativeExtension K L`, continuous `algebraMap`) inside `Ksep`,
  `inv_L (res x) = [L : K] • inv_K x`.
- `continuous_spectral_algHom`, `valuativeExtension_self`, `valuativeExtension_spectral_algHom`:
  a `K`-algebra map between finite extensions of `K` is continuous and respects the valuations for
  the Library's spectral local-field structures (`Langlands.LocalField.FiniteExtension`).
- `openInvariant K U : H²(U, Ksepˣ) ≃+ ℚ/ℤ`: the invariant of the fixed field of `U` (with its
  spectral local-field structure) through `openCohomologyIso` (`openInvariant_apply`).
- `resOfLE_comp_openCohomologyIso h n`: restriction between open subgroups `V ≤ U` is restriction
  between their fixed fields.
- `openInvariant_resOfLE U V h x`: `inv_V (res x) = [U : V] • inv_U x`.

## Source and licence

The open-subgroup section is ported from `src/GroundTheory/ProfiniteCohomology/LocalClassFormationAlt.lean`
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`: declarations
`fixingSubgroup_fixedField_openSubgroup`, `finiteDimensional_fixedField_openSubgroup`,
`index_openSubgroup`, `fixedField_le_fixedField`, `relIndex_eq_finrank`, `galFixedFieldToOpen`,
`galFixedFieldEquivOpen`, `galUnitsOpenHom` (here `unitsModuleOpenHom`), `openCohomologyIso`,
`cohomologyResLE_comp_openCohomologyIso` (here `resOfLE_comp_openCohomologyIso`, with the
Library's restriction `unitsRestriction` in place of the source's `galUnitsResScalars`),
`isZero_H1_open` (here `isZero_cohomology_one_res_unitsModule`), `localInv`, `localInv_res` (here
`openInvariant`, `openInvariant_resOfLE`). The repository has no licence file; its text is used
with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Replaced notions: the source's invariant `brauerInv` and its construction (twelve files of its
`LocalClassFormation/`, with its own local class field theory) are replaced by the Library's
`localBrauerInvariant` (`Langlands/ClassFieldTheory/Local/BrauerLocalInvariant.lean`) and its
scalar-extension law `localBrauerInvariant_scalarExtension`; the source's valuation on the
separable closure (`algebraicValuativeRel`, `algebraicTopology`), used to make the fixed fields
local fields, is replaced by the Library's spectral structure on finite extensions. The
restriction law is proved here from the Library's `brauerContinuousEquiv_scalarExtension` and the
naturality of the comparison with continuous cohomology (`isoContinuousCohomology_naturality`).
`invariant`, `invariant_brauerEquiv`, `unitsRestriction` and its lemmas are new.

## References

- J.-P. Serre, *Local Fields*, chapter XII, §3 (the Brauer group of a local field), pp. 184–187, and
  chapter XIII, §3, pp. 192–194.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §1 (cohomology
  of the multiplicative group), pp. 371–377.
