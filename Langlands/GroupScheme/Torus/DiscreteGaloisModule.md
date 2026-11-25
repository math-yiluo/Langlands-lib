# Finitely generated discrete absolute-Galois modules

This construction supplies the module category used in the absolute-Galois
classification of groups of multiplicative type. It reuses the published
`Langlands.SmoothRep` category and its open-stabilizer definition.

## Objects and universes

For a field `k : Type u`, the acting group is exactly
`SeparableClosure k ≃ₐ[k] SeparableClosure k`, with Mathlib's Krull topology.
`SeparableClosure k` is the chosen separable closure inside the algebraic
closure. The construction does not identify this automorphism group with
Mathlib's differently presented `Field.absoluteGaloisGroup`.

`fgDiscreteGaloisModuleProperty.{u,v} k` is the property `Module.Finite ℤ A`
of an object of the existing category
`SmoothRep.{0,u,v} ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k)`.
`FGDiscreteGaloisModule.{u,v} k` is its full subcategory. Thus its objects are
actual abelian groups in `Type v`, with their integral module structures and
actual integral representations, such that the module is finitely generated
over the integers and each vector is fixed by an open subgroup. The module
universe `v` is independent of the field universe `u`. The object type lives
in `Type (max u (v + 1))`; no smallness or resizing is asserted.

Finite generation imposes no freeness or torsion-free condition. In particular
the category permits the torsion modules required for finite nonsmooth
diagonalizable groups in positive characteristic. There is no algebraic group
smoothness or characteristic hypothesis in this module construction.

## Interfaces

The carrier coercion, additive group, integral module, and finite-generation
instance expose the underlying module. `representation` exposes its exact
algebraic action; `isSmooth` recovers the open-subgroup condition.
`of` bundles any finitely generated integral representation with this condition.

`toSmoothRep` is the full-subcategory inclusion; `toRep` composes it with the
published smooth-category inclusion into Mathlib's algebraic `Rep` category.
Both are fully faithful, and explicit `Full` and `Faithful` instances for the
composite are supplied. Objects and maps retain their actual actions and linear
maps. `hom` and `ofHom` identify morphisms with all equivariant integral linear
maps, with inverse, identity and composition laws given by the definitions.
No choice of splitting field or character realization is part of an object.

## Discrete continuity

No topology on the underlying modules is installed globally. Given any supplied
discrete topology on an object's carrier, `continuous_orbitMap` proves continuity
of every orbit map. It applies the published theorem
`Langlands.isSmoothVector_iff_continuous_orbitMap` to `isSmooth`.
`continuous_action` then uses Mathlib's `continuous_prod_of_discrete_right`
to obtain joint continuity on the product of the Krull group and the discrete
module. `continuousAction` bundles this same action as a continuous map, and
`continuousAction_apply` records its value.

Conversely, `ofContinuous` takes a finitely generated integral representation
with a supplied discrete carrier topology and a proof of joint continuity.
Composition with `σ ↦ (σ,m)` gives the continuous orbit map for each `m`;
the reverse implication of the same published theorem supplies smoothness.
The topology is used to justify membership and is not stored in the object.
These constructions implement both continuity descriptions on the same
underlying representations. All module morphisms are continuous when the
carriers have discrete topologies.

## Provenance and remaining work

The registered original source is J. S. Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 12.g, printed p.239 / PDF p.255, describes the Krull automorphism group
of a separable closure and characterizes its discrete continuous modules by
open subgroups fixing each element. Theorem 12.23, printed p.240 / PDF p.256,
uses finitely generated integral modules with this action as the target of
the character anti-equivalence. Both original pages and the complete retained
official 2017 errata snapshot were read; no listed correction changes these
passages.

This is a derived categorical packaging of that target. The categorical
inclusions and morphism laws reuse
[the published smooth category](../../Representation/Category/Basic.md).
The continuity arguments reuse
[the published discrete-orbit proof](../../Representation/Smooth/DiscreteOrbitProof.md)
and Mathlib's elementary product-continuity theorem.
Mathlib supplies the chosen separable closure, Krull topology and its
topological-group instance. No classification theorem is used as a Lean proof.

This module supplies the target category and its intrinsic interfaces. Constructing
the actual character functor into it, proving finite generation and continuity
for those actual characters, and proving the absolute-Galois anti-equivalence
remain separate obligations.
