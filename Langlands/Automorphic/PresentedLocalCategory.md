# Irreducible admissible classes of actual presented local components

This internal construction refines the actual local components of
`PresentedLocalComponent.lean` to objects and classes in the existing
irreducible admissible category, with explicit irreducibility and admissibility
hypotheses on the local factor.

## Inputs and provenance

The field is a number field `F : Type uF`, the matrix rank is any natural number,
and the coefficients are complex. The model spaces `V v : Type uV` have an
independent carrier universe. Their algebraic representations use the actual
completed-local general linear groups with the existing topology. No topology
or finite-dimensionality hypothesis is imposed on their carriers.

The supplied tensor presentation is a genuine equivariant equivalence onto an
actual finite invariant subspace of automorphic forms. Nonzeroness of that
subspace remains an explicit hypothesis. The published component construction
then supplies an actual embedded local subspace, its smoothness, and a genuine
equivalence from the specified factor.

The provenance is internal. The module reuses the published
`isIrreducible_iff_of_equiv`, `isAdmissible_iff_of_equiv`,
`fixedVectorsEquiv`, and `fixedVectors_ne_bot_iff_of_equiv`, and the existing
full subcategory and quotient constructions in `Category.Basic` and
`Category.ClassInvariants`. It introduces no external-literature assertion.

## Actual local objects and quotient equality

For any actual `LocalRealization`, `IsIrreducible` abbreviates irreducibility
of its local action: simplicity of the invariant-subspace lattice, including
nonzeroness. `IsAdmissible` abbreviates the existing convention of smoothness
and finite generation of the fixed space for every open subgroup.

`irreducibleAdmissible` bundles this actual form subspace with supplied proofs
of both properties. `dualClass` takes its existing `SmoothDualClass`, the
quotient by genuine isomorphisms in the irreducible admissible full subcategory.
Both objects use the form-carrier universe `uF`.

`dualClass_eq_iff` identifies equality with existence of a genuine equivariant
linear equivalence of the two actual subspaces. The proof forgets an isomorphism
to the smooth category in one direction and lifts a smooth isomorphism to the
full subcategory in the other. Thus `dualClass_eq_iff_isoClass_eq` identifies
refined class equality with equality of the underlying smooth classes.
`dualClass_hasFixedVector_iff` unfolds the existing quotient fixed-vector
predicate at this actual representative.

## Presented components

`localComponent_isIrreducible_iff` and `localComponent_isAdmissible_iff`
transfer the two properties in both directions through `localComponentEquiv`.
They do not deduce either property from a nonzero global presentation.
`localComponentFixedEquiv` restricts that equivalence to the fixed spaces of
any supplied subgroup, without requiring the subgroup to be open or compact.

`localComponentObject` and `localComponentDualClass` use explicit proofs that
the specified factor is irreducible and admissible. The representative remains
the actual embedded form subspace in `uF`, regardless of `uV`.
`localComponentDualClass_eq` compares two nonzero presentations of the same
tensor data, even into different actual global subspaces. It applies the
published equality of their smooth classes and the refined-class equality
criterion above. That criterion also carries the published independence of a
nonzero tensor-tail choice to any such irreducible admissible slices.

`localComponentDualClass_hasFixedVector_iff` says that the class has a nonzero
vector fixed by a supplied subgroup exactly when the specified model factor
does. It uses fixed-space invariance under the genuine local equivalence.
Outside the exceptional set, `localComponentDualClass_hasIntegralFixedVector`
applies this criterion to the actual integral local subgroup and uses the
presentation's nonzero reference vector and its supplied invariance.

## Scope

These are conditional constructions from a genuine presentation and explicit
local irreducibility and admissibility. They do not prove factorization
existence, irreducibility or admissibility of arbitrary automorphic local
factors, uniqueness across different factor families, or a fixed-space
dimension-one theorem. The integral-fixed-vector conclusion uses the existing
smooth-dual predicate; no normalized Satake parameter or Hecke eigenvalue is
constructed here. Global central-character and cuspidal conditions remain
properties of the embedded forms, as in the preceding component module.
