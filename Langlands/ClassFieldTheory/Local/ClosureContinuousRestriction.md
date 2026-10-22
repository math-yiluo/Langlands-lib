# Closure transport through the named continuous restriction

Authors: Worker 263 and Worker 134. Worker 263 wrote this module; Worker 134
proposed the definitional bridge and wrote the imported `ClosureCohomologyTransport`.

This module restates the published compatible-closure cohomology transport of
`ClosureCohomologyTransport` in terms of the Library's named restriction map
`Langlands.Continuous.continuousRestriction` for the discrete closure-unit module
`absoluteUnitDiscreteModule K`. It then specializes the transport to the bundled
open normal fixing subgroup `finiteGaloisFixingSubgroup K E` of a finite Galois
intermediate field. It constructs no new cohomology map: every declaration is
either a definitional identity or the core module's construction or certificate,
reused by import, with a restated type. The universe `u` of `K` is arbitrary.

## Bridge to the named restriction

`closureSubgroupRestriction_eq_continuousRestriction` states that, for every field
`K`, every intermediate field `E` of `AlgebraicClosure K` and every degree `q`,
the core's `closureSubgroupRestriction K E q` equals
`continuousRestriction (absoluteUnitDiscreteModule K) E.fixingSubgroup q`. Both
are `ContinuousCohomology.map` of `subgroupInclusion E.fixingSubgroup` with the
identity coefficient morphism. Their coefficient objects agree definitionally:
`DiscreteModule.restrict` is an abbreviation whose underlying topological
representation is `TopRep.res E.fixingSubgroup.subtype` of the module's own
representation, and the representation of `absoluteUnitDiscreteModule K` is
`absoluteUnits K`. The proof is therefore `rfl`. This statement needs neither
characteristic zero, nor normality, nor the closure-inclusion instances.

## Restatements at the fixing subgroup

From here on `K` has characteristic zero and `E` is normal over `K`. The
statements quantify over exactly the core's
`[Algebra (AlgebraicClosure K) (AlgebraicClosure E)]` and
`[IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]`. They impose no
compatibility between this embedding and the canonical embedding of `E` into
its own algebraic closure.

- `continuousRestriction_comp_closureSubgroupCohomologyMap`: the named
  restriction to `E.fixingSubgroup` followed by `closureSubgroupCohomologyMap K E q`
  is `absoluteRestriction K E q`.
- `closureSubgroupCohomologyEquiv_continuousRestriction`: the same identity on an
  arbitrary class `x`, with the continuous linear equivalence
  `closureSubgroupCohomologyEquiv K E q`.
- `absoluteRestriction_eq_zero_iff_continuousRestriction`: `x` vanishes under
  absolute restriction exactly when it vanishes under the named restriction.
- `absoluteRestriction_ker_eq_continuousRestriction_ker`: the two maps have
  equal `LinearMap.ker` submodules of `absoluteCohomology K q`.

Each proof is the corresponding core theorem (`closureSubgroupRestriction_comp`,
`closureSubgroupCohomologyEquiv_restriction`,
`absoluteRestriction_eq_zero_iff_subgroup`, `absoluteRestriction_ker_eq_subgroup`),
accepted for the restated type through the definitional bridge. As in the core,
these statements are elaborated with
`set_option backward.isDefEq.respectTransparency false`: without it, Lean fails
to synthesize the group structure on the bare subtype `↥E.fixingSubgroup` in the
cohomology types.

## Finite Galois specialization

In the last section `E` is finite-dimensional and Galois over `K`. Normality is
then inferred from `IsGalois`, and the same two closure-inclusion instances are
quantified. The subgroup is written as
`(finiteGaloisFixingSubgroup K E).toSubgroup`, the published open normal bundle
whose carrier is `E.fixingSubgroup` (`finiteGaloisFixingSubgroup_toSubgroup` holds
by `rfl`). The source coefficients are
`((absoluteUnitDiscreteModule K).restrict (finiteGaloisFixingSubgroup K E).toSubgroup).toTopRep`,
the target of the named restriction.

- `finiteGaloisFixingCohomologyIso K E q` is the core isomorphism
  `closureSubgroupCohomologyIso K E q` from the continuous cohomology of the
  restricted module to `absoluteCohomology E q`. Its inverse and inverse
  identities are those of the core construction.
- `finiteGaloisFixingCohomologyIso_hom` identifies its forward morphism with
  `closureSubgroupCohomologyMap K E q`, by the core's `closureSubgroupCohomologyIso_hom`.
- `finiteGaloisFixingCohomologyEquiv` is the continuous linear equivalence over
  `IntegerScalars` extracted from this isomorphism, and
  `finiteGaloisFixingCohomologyAddEquiv` is its underlying additive equivalence.
- `continuousRestriction_comp_finiteGaloisFixingCohomologyIso`: the named
  restriction to the open normal fixing subgroup followed by the forward
  morphism of the isomorphism is `absoluteRestriction K E q`.
- `finiteGaloisFixingCohomologyEquiv_continuousRestriction` and
  `finiteGaloisFixingCohomologyAddEquiv_continuousRestriction` are the pointwise
  forms for the linear and additive equivalences.
- `absoluteRestriction_eq_zero_iff_finiteGaloisFixing` is the vanishing criterion.
- `absoluteRestriction_ker_eq_finiteGaloisFixing_ker` is the equality of
  `LinearMap.ker` submodules, and
  `absoluteRestriction_addMonoidHom_ker_eq_finiteGaloisFixing_ker` is the equality
  of the kernels of the underlying additive maps (`AddMonoidHom.ker`), the form
  used by `AbsoluteH2InflationStatement`. The latter is proved by
  extensionality from the vanishing criterion.

The definitions and the other theorems are again the core terms. Since these
statements mention the subgroup only through the bundled open normal subgroup,
they elaborate without the transparency option. The kernel equalities have no
premise beyond the section's hypotheses.

## Provenance and scope

This is derived internal infrastructure. The underlying construction and all its
certificates (the continuous group equivalence onto the fixing subgroup, the
coefficient isomorphism with its equivariance, continuity and inverse
certificates, the cohomology isomorphism and the map identity) are Worker 134's
published `ClosureCohomologyTransport` and the modules it imports. They are
imported here by Lean name, not copied. The named restriction and
`DiscreteModule.restrict` come from the published
`Langlands.Cohomology.Continuous.FiniteQuotientSystem`, and
`absoluteUnitDiscreteModule` and `finiteGaloisFixingSubgroup` from the published
`FixedFieldStages`.

The mathematical context is Serre, *Local Fields* (1979), Chapter X, section 4,
printed page 156 / PDF page 162. There, a `k`-monomorphism `f` of `K` into `K'`
defines `f* : G' → G` with `f ∘ s = s' ∘ f`, compatible with `f : K* → K'*`, and
inducing maps `H^q(K/k) → H^q(K'/k')`. The proof of Proposition 6 restricts from
`G = G(L/k)` to `H = G(L/K)` and reads `H^2(H, L*)` as `H^2(L/K)`. Here the base
field is `K`, its intermediate field is `E`, and the supplied inclusion
`AlgebraicClosure K → AlgebraicClosure E` plays the role of `f`; this module
supplies that identification of subgroup restriction with absolute restriction
in every degree `q`, at the actual fixing subgroup. The registered source is
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The module makes no assertion comparing two different closure embeddings (Serre's
Proposition 5) and does not prove the exact sequence of Proposition 6, its
corollary, or absolute degree-two inflation exactness. Existing published
Lean/Markdown pairs are unchanged.
