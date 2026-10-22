# Finite-extension descent along a directed union of fields

Authors: Worker 29; Worker 10 supplied the requested strengthened formulation.

`Langlands.FieldTheory.FiniteExtensionDirectedUnionDescent` is a proposition
definition, not a theorem or a supplied descent certificate.

## Exact statement

Let `L` and `M` be fields in an arbitrary common universe `u`, with an
algebra structure `Algebra L M` and `FiniteDimensional L M`. Let `I` be a
nonempty type in an independent universe `v`, and let `A : I → Subfield L`.
Assume `Directed (· ≤ ·) A`, meaning that any two members are contained in
some member, and assume that every element of `L` belongs to some `A i`.
There is no order on the index type itself and no common ground field or
finite-dimensionality assumption on the stages.

For every initial index `i₀ : I` and finite set `s : Finset M`, there exist
an index `i : I` with `A i₀ ≤ A i` and an intermediate field
`B : IntermediateField (A i) M` such that all of the following hold:

1. `B` is finite dimensional over `A i`, and
   `Module.finrank (A i) B = Module.finrank L M`.
2. `B.LinearDisjoint L`: inside `M`, the field `B` and the specified image
   of `L` are linearly disjoint over `A i`.
3. `IntermediateField.adjoin L (B : Set M) = ⊤`; thus the compositum of
   `B` and the image of `L` is all of `M`.
4. Every element of `s` belongs to `B`.
5. If `Algebra.IsSeparable L M`, then `Algebra.IsSeparable (A i) B`.
6. If `IsGalois L M`, then `IsGalois (A i) B`.

The last two implications concern the **same** existential witness `i, B`
as all the preceding conclusions. Every field, instance, family,
hypothesis, initial index, and finite set is quantified inside the
proposition; its only external parameters are the universe levels.

## Scalar structures

The statement explicitly installs `Algebra (A i) L` and
`Algebra (A i) M` using Mathlib's `Algebra.ofSubsemiring (A i)`.
These use, respectively, the literal subfield inclusion `(A i).subtype`
and `(algebraMap L M).comp (A i).subtype` as their algebra maps, with
the inherited scalar actions. It explicitly installs
`IsScalarTower (A i) L M` using the equality of these algebra maps.
The algebra structures from `A i` to `B` and from `B` to `M` are the
canonical ones attached to the intermediate field; their compatible
`IsScalarTower (A i) B M` is explicitly installed as well. No alternative
scalar action is quantified or assumed.

Mathlib's `IntermediateField.LinearDisjoint` takes one intermediate field
and one abstract field in a scalar tower. Here it means linear disjointness
of `B.toSubalgebra` and the range of
`IsScalarTower.toAlgHom (A i) L M`. The `adjoin` conclusion uses the given
`L`-algebra structure on `M`. Thus these two clauses use the actual
embeddings into `M`, even when `L` is not presented as a subtype of `M`.

## Source and derived strengthening

Source: Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979,
Chapter V, §4, Lemma 6 and its proof, printed page 89 (PDF page 96).
The registered source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The original lemma and proof were read, together with the surrounding
printed pages 88–90. No project errata note for this source was found.

Serre states the existence of a stage extension of the same degree,
linear disjointness, the compositum equality, and separable and Galois
refinements. The initial-stage and finite-set clauses are derived
strengthenings, not additional quotations from the lemma. The following
explains their mathematical provenance; it is not a Lean proof.

Choose an `L`-basis of `M` containing `1`. There are finitely many
coefficients expressing products of basis elements and elements of `s`
in this basis. Covering and directedness give a stage containing all those
coefficients and containing `A i₀`. The span of the basis over this stage
is a finite-dimensional subalgebra of the field `M`, hence is a field.
Its basis remains independent over `L`, yielding the stated degree and
linear disjointness; its `L`-span is `M`, and it contains `s`.

For separability, Serre's proof descends it using linear disjointness
from the purely inseparable extension obtained by adjoining roots in
positive characteristic; in characteristic zero it is automatic. For
the Galois refinement, further include the finitely many coefficients of
the images of the basis under all elements of the finite Galois group.
The same basis span at this enlarged stage is then invariant under those
automorphisms. Their restrictions give as many distinct automorphisms as
the degree, so the descended extension is Galois. Enlarging the stage in
this way preserves containment of `A i₀`, the elements of `s`, the basis
and degree, and the other conclusions. This explains how both conditional
refinements can be required of one witness.

## Scope and remaining obligations

This file only states the proposition. Constructing the descended field
and proving all of its properties remains a separate proof obligation.
Serre's eventual uniqueness assertion is omitted.

The target is a generic prerequisite for the finite-norm argument leading
to inertia second-cohomology vanishing. It supplies neither simultaneous
descent of a finite tower nor the local identification with a maximal
unramified extension from Lemma 7. Those are downstream obligations.
No valuation, inertia, norm, local-field, or prior base-change certificate
is an input to this proposition.

The only import is `Mathlib.FieldTheory.LinearDisjoint`, in the pinned
Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment.
