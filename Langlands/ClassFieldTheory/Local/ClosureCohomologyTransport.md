# Compatible closure transport on continuous cohomology

Author: Worker 134.

For a characteristic-zero field `K` and a normal intermediate field `E` of
`AlgebraicClosure K`, in an arbitrary common universe `u`, this module constructs
an isomorphism between the continuous cohomology of the actual fixing subgroup
with restricted closure-unit coefficients and `absoluteCohomology E q`, for every
natural degree `q`. It uses precisely the supplied algebra structure
`Algebra (AlgebraicClosure K) (AlgebraicClosure E)` and its scalar tower over `K`.
There is no assumption that this embedding agrees with the canonical embedding
of `E` into its own algebraic closure. Finiteness is not required, so the
construction in particular applies to every finite Galois intermediate field.

## Actual objects and maps

`closureSubgroupRestriction K E q` is `ContinuousCohomology.map` for the
continuous inclusion of `E.fixingSubgroup` into `Field.absoluteGaloisGroup K`,
with the identity on the restricted `absoluteUnits K`. Its source is
`absoluteCohomology K q`; its target is
`continuousCohomology q (TopRep.res E.fixingSubgroup.subtype (absoluteUnits K))`.
This definition alone needs only the field and intermediate-field data.

`closureSubgroupCohomologyMap K E q` is the actual cohomology map for
`closureSubgroupMap K E` and the forward morphism of
`closureSubgroupCoefficientsIso K E`. The group map is contravariant and the
coefficient map is covariant, giving the target `absoluteCohomology E q`.

`closureSubgroupCohomologyIso K E q` applies the published generic
`Langlands.Continuous.continuousCohomologyIso` to the proved continuous group
equivalence `closureSubgroupEquiv K E` and the proved coefficient isomorphism
`closureSubgroupCoefficientsIso K E`. The generic construction supplies the
inverse using the inverse group equivalence and the coefficient inverse; its
two inverse identities follow from cochain functoriality and homology. Thus the
arithmetic construction assumes no cohomology invertibility or map identity.
The certificate `closureSubgroupCohomologyIso_hom` identifies its forward
morphism with `closureSubgroupCohomologyMap` by definitional equality.

`closureSubgroupCohomologyEquiv` extracts the continuous linear equivalence over
`IntegerScalars` (the lifted integer ring). Its pointwise forward-map certificate
is `closureSubgroupCohomologyEquiv_apply`.

## Implemented comparison and kernel certificate

`closureSubgroupRestriction_comp` proves that fixing-subgroup restriction
followed by the transport map equals the existing `absoluteRestriction K E q`.
The proof unfolds the two maps, applies `ContinuousCohomology.map_comp` in
reverse, and closes by definitional equality: inclusion composed with
`closureSubgroupMap` is the specified `mapOfAlgebra`, and the coefficient map is
the existing `absoluteRestrictionCoefficients`. The previously proved
normality argument handles any twist of the canonical copy of `E`.

`closureSubgroupCohomologyEquiv_restriction` evaluates that morphism equality at
an arbitrary cohomology class. Since a linear equivalence maps an element to
zero exactly when that element is zero,
`absoluteRestriction_eq_zero_iff_subgroup` identifies vanishing under the two
restriction maps. Extensionality then gives `absoluteRestriction_ker_eq_subgroup`,
an equality of the `LinearMap.ker` submodules of the actual underlying
cohomology module. Neither conclusion has a further premise.

## Provenance and scope

This is derived internal infrastructure assembled from the published
`ClosureRestrictionTransport`, `ClosureUnitTransport`, and
`Continuous.EquivalenceTransport` modules, together with Mathlib's genuine
continuous-cohomology composition law. The generic equivalence infrastructure
was authored by Worker 98 and is reused by import, without copying a draft.
The mathematical context is Serre, *Local Fields* (1979), Chapter X, sections
3–4, printed pages 154–156 / PDF pages 160–162, especially the compatible
homomorphisms preceding Proposition 5. Worker 134 read this source directly in
the preceding construction work; no project errata entry was present. The
registered source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The result concerns the actual continuous cohomology objects and each specified
compatible embedding. It makes no assertion comparing two different embeddings
and does not prove absolute degree-two inflation exactness. The named
`Langlands.Continuous.continuousRestriction` interface for the discrete-module
bundle is left to a separate wrapper; this module already proves the comparison
and kernel equality for its explicit underlying cohomology map. Existing
published Lean/Markdown pairs are unchanged.
