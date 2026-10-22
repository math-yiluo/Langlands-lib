# Transport on topological abelianizations

Author: Worker 20.

This module constructs the topological equivalence of abelianizations induced
by a supplied topological group equivalence. It uses the existing
`TopologicalAbelianization G`, the quotient by the closure of the commutator
subgroup, with its actual quotient topology. It is infrastructure for comparing
separately presented Weil groups with their images in a common algebraic
closure. The groups and their carrier universes are arbitrary.

## Construction and identities

The published `abelianizationMap f` descends the composite of a continuous
homomorphism `f` with the target quotient projection. Its closed-kernel argument
is already proved in `Langlands.ClassFieldTheory.Local.Galois`.
`abelianizationMap_projection` records its value on every quotient generator.
`abelianization_hom_ext` proves equality of continuous homomorphisms out of
the quotient by checking them after the surjective projection.

`abelianizationMap_id` and `abelianizationMap_comp` prove the identity and
composition laws. Each proof reduces an arbitrary quotient element to a
representative using quotient induction; the equality on representatives is
definitional.

For a supplied `e : G ≃ₜ* H`, `abelianizationCongr e` is the actual
continuous group equivalence

```
TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H.
```

Its forward map is `abelianizationMap e`; its inverse is
`abelianizationMap e.symm`. Both are already continuous. Quotient induction
reduces their inverse laws to cancellation of `e` with `e.symm`.
`abelianizationCongr_projection` identifies its action on representatives.
`abelianizationCongr_symm`, `abelianizationCongr_refl` and
`abelianizationCongr_trans` prove compatibility with inverse, identity and
composition.

For a continuous homomorphism `χ : H →ₜ* A` into a T1 commutative group,
`abelianizationLift_comp` proves that descent of `χ ∘ f` equals descent of
`χ` after `abelianizationMap f`. The only topology on `A` needed here is the
one already required by the published lift: T1 ensures its kernel is closed.
`abelianizationLift_comp_equiv` specializes this identity to the constructed
equivalence. These identities also follow by quotient induction and
definitional computation on representatives.

## Provenance and scope

This is a derived construction from the published
`Langlands.ClassFieldTheory.Local.Galois` interface, particularly
`abelianizationProjection`, `abelianizationLift`, `abelianizationLiftEquiv`
and `abelianizationMap`. The quotient implementation comes from the project's
pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The new inverse, composition and
descent identities are intrinsic construction proofs described above; no
external arithmetic theorem is invoked.

The input `e` must be an actual topological group equivalence. This module
constructs no local reciprocity map, no field-embedding comparison and no
local constant. In a later field comparison, it supplies the abelianized
transport only after the corresponding Weil-group equivalence has been
constructed. It makes no assertion that independently chosen field or closure
embeddings are coherent.
