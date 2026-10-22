# Compactness of the full-closure absolute Galois group

Author: Worker 29.

`Langlands.GaloisRepresentation.absoluteGaloisGroupCompactness.{u}` proves exactly
`Langlands.GaloisRepresentation.AbsoluteGaloisGroupCompactness.{u}`, imported
from `Langlands.Galois.AbsoluteTopologyStatement`. Thus for every field
`K : Type u`, including imperfect fields, the actual
`Field.absoluteGaloisGroup K` is compact in its existing Krull topology.
There are no additional premises. The statement and its imported pairs are
unchanged.

## Implemented proof

Write `L = AlgebraicClosure K` and let `P = perfectClosure K L`, Mathlib's
relative perfect closure as an intermediate field of `L/K`. The inherited
algebra maps are the original inclusion maps, with their scalar tower.
Mathlib's `perfectClosure.perfectField` makes `P` perfect because `L` is
algebraically closed, hence perfect. The extension `L/P` is algebraic and
normal, and its perfect base makes it separable. Consequently it is Galois,
and the compactness instance in `Mathlib.FieldTheory.Galois.Profinite`
applies to `Gal(L/P)`.

Two private helper theorems justify transfer to the requested group:

1. `continuous_restrictScalars` proves continuity of the existing group
   homomorphism `AlgEquiv.restrictScalarsHom K : Gal(L/P) →* Gal(L/K)` for
   any field tower with `L/P` algebraic. Continuity of group homomorphisms
   reduces to continuity at the identity. By
   `krullTopology_mem_nhds_one_iff`, a target neighborhood contains the
   subgroup fixing some finite intermediate extension `E/K`. Finite
   dimensionality supplies a finite generating set `s` for `E` through
   `IntermediateField.essFiniteType_iff`. The field `P(s)` is finite over
   `P`, since `L/P` is algebraic. Its fixing subgroup is a source
   neighborhood. Any automorphism in that subgroup fixes `s`; after
   scalar restriction it therefore fixes `K(s) = E`. This gives the
   required neighborhood containment in the actual Krull topologies.
2. `restrictScalars_surjective_of_purelyInseparable` proves surjectivity
   for any tower with `P/K` purely inseparable. For a `K`-automorphism
   `σ` of `L`, the composite of `σ` with `P → L` and the inclusion
   `P → L` are `K`-algebra homomorphisms. Mathlib's uniqueness instance
   for homomorphisms from a purely inseparable extension into a reduced
   algebra makes them equal. Hence `σ` fixes `P` pointwise and can be
   regarded as a `P`-automorphism without changing its underlying map.
   Its scalar restriction is the original `σ`.

`perfectClosure.isPurelyInseparable` supplies the hypothesis of the second
helper. Finally `Function.Surjective.compactSpace` transfers compactness
along the continuous surjection from `Gal(L/P)` onto `Gal(L/K)`. The latter
is definitionally the full-closure absolute Galois group in the target.
No topology is replaced and no separable-closure comparison is assumed.
The helpers allow independent universes for the three fields; the final
closed theorem has the single arbitrary universe of its published target.

## Source and provenance

Serre, *Local Fields* (1979), Chapter X, Section 3, printed page 154
(PDF page 160), states compactness of an infinite Galois group's Krull
topology via the inverse limit of finite Galois groups. Registered source:
`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained original `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The cited paragraph was checked in the original. No source-specific erratum
is present in the current Library.

This proof is an explicit derived adaptation to the full algebraic closure
of an arbitrary field. Serre's Galois-extension result is used through
Mathlib for `L/P`; it is not applied to a possibly inseparable `L/K`.
The perfect-closure and continuous-surjection arguments above are the
implemented bridge. Mathlib dependencies are those of the prepared
project environment, commit `5ed2965256430c3649e86755f9576b54eca72435`.
This module establishes compactness only; it makes no cohomological or
local class-field-theoretic claim.
