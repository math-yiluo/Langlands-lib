# The open image of absolute Galois restriction

Author: Worker 134.

This module constructs the actual open image of
`Field.absoluteGaloisGroup.mapOfAlgebra K L` for every finite extension `L/K`
of characteristic-zero fields in an arbitrary common universe `u`. It uses
exactly the supplied algebra structure from `AlgebraicClosure K` to
`AlgebraicClosure L` and its scalar tower over `K`. There is no normality
hypothesis on `L/K`, no additional closure tower over `L`, and no assumed
openness, equivalence, injectivity, or index identity. Existing published
modules are unchanged.

All names below are in
`Langlands.ClassFieldTheory.Local.AbsoluteRestriction`. The construction has
parameters `K L : Type u`, fields, `Algebra K L`, `FiniteDimensional K L`,
`Algebra (AlgebraicClosure K) (AlgebraicClosure L)`, and
`IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)`. The topological
multiplicative equivalence and the index formula additionally require
`CharZero K`. This implies characteristic zero for `L` internally.

## Public interface

- `closureEquiv K L : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure L`
  upgrades the supplied algebra map to an equivalence.
  `closureEquiv_apply` identifies its forward map with that exact algebra map,
  so it can be reused for actual unit coefficient transport.
- `fieldEmbedding K L : L →ₐ[K] AlgebraicClosure K` sends canonical `L` in
  its own closure through the inverse closure equivalence.
  `closureEquiv_fieldEmbedding` gives the commuting equation.
- `imageField K L` is the range of this embedding, and
  `imageFieldEquiv K L : L ≃ₐ[K] imageField K L` identifies it with `L`.
  The finite-dimensional instance and `imageField_finrank` retain its degree.
- `openSubgroup K L : OpenSubgroup (Field.absoluteGaloisGroup K)` is the
  fixing subgroup of this actual image field. `openSubgroup_eq_range` proves
  that its underlying subgroup equals the range of the specified
  `mapOfAlgebra K L`. `range_isOpen` also states openness of this range directly.
- `groupEquiv K L : Field.absoluteGaloisGroup L ≃ₜ* openSubgroup K L`
  is the required continuous multiplicative equivalence.
  `groupEquiv_subtype` identifies subgroup inclusion composed with its
  underlying homomorphism with the specified restriction homomorphism.
  `groupEquiv_apply_val` is the pointwise identity.
- `index_eq_finrank` states
  `(openSubgroup K L).toSubgroup.index = Module.finrank K L`.

`subgroupMap` is the actual continuous restriction with restricted codomain;
`subgroupMap_commutes` is its field-level commuting square. The explicit
`subgroupInverse` conjugates through `closureEquiv`.
`subgroupMap_left_inverse` and `subgroupMap_right_inverse` prove both inverse
identities, and `subgroupMulEquiv` bundles the algebraic equivalence.
`map_injective` states injectivity of the original restriction map directly.

## Implemented construction

The upper closure is integral over `L`, hence over `K`, and then over the lower
closure by the scalar tower. An integral extension of an algebraically closed
field has bijective algebra map. This gives `closureEquiv` with its exact
forward-map certificate.

Pulling the canonical embedding of `L` back through that equivalence produces
`fieldEmbedding` and its actual image field. This field is not asserted equal
to any independently chosen copy of `L` inside `AlgebraicClosure K`.
The equivalence to its field range transfers finite dimension and degree.

The normal-restriction commuting square shows that every image automorphism
fixes this image field. Conversely, a fixing automorphism conjugated through
`closureEquiv` fixes canonical `L`, hence belongs to its absolute Galois group.
Cancellation of the closure equivalence gives both inverse identities.
They also show that the fixing subgroup is exactly the range, with no
surjectivity premise. Its openness follows from finiteness of the image field
using `IntermediateField.fixingSubgroup_isOpen`.

Restriction is continuous for the Krull topologies, and its codomain restriction
inherits continuity through the subgroup topology. In characteristic zero the
upper algebraic closure is Galois over `L`, so its automorphism group is compact.
The target is Hausdorff. The inverse of this continuous bijection is therefore
continuous. Finally,
`IntermediateField.finrank_eq_fixingSubgroup_index` applied to the actual image
field in the Galois closure of `K`, followed by `imageField_finrank`, proves
the index formula without normality of that image field.

## Provenance and scope

This is a derived internal construction from Mathlib's algebraic closure,
normal restriction, infinite Galois correspondence, Krull topology, and
compact-to-Hausdorff inverse-continuity results. Its inverse-conjugation proof
adapts Worker 134's published `ClosureRestrictionTransport` construction from
a canonical normal intermediate field to the actual image field, removing
the need for normality of `L/K` while preserving the specified map.

The field/group conventions agree with Jean-Pierre Serre, *Local Fields*
(1979), Chapter X, sections 3–4, printed pages 154–156 / PDF pages 160–162.
Chapter XI, section 1, printed pages 164–166 / PDF pages 170–172 provides the
finite-extension/subgroup setting. Worker 134 read these original pages.
The registered source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 134 also read the *Local Fields* entries on PDF pages 2–3 of the
registered `serre-book-corrections-2019`; none changes the cited passages.
No project-specific errata file for the 1979 source was found.

The precise range homeomorphism and index certificates here are derived
constructions, not assertions attributed to a numbered theorem in Serre.
The module constructs no cohomological transfer, invariant, or reciprocity
map and claims none of their laws or existence statements.
