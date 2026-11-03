# Source categorical finiteness for smooth representations

Worker 1212. This proof establishes the exact published proposition
`Langlands.SmoothRep.RenardFinitenessStatement`, imported from
[RenardFinitenessStatement](RenardFinitenessStatement.md). The proof theorem is
`Langlands.SmoothRep.renardFinitenessStatement`.

For every commutative ring `R`, group `G` with a supplied topology and
topological-group instance, and actual smooth representation `A`, it proves
both equivalences in the published conjunction:

- `Langlands.Renard.IsFiniteTypeObject A` if and only if
  `Module.Finite R[G] A.representation.asModule`.
- `Langlands.Renard.IsFiniteLength A` if and only if `A.HasFiniteLength`,
  the existing group-algebra module finite-length predicate.

The coefficient, group and carrier universes `uR`, `uG`, `uV` remain
independent. There are no additional premises. In particular the theorem
includes zero representations and the zero ring; no nontriviality, finite
dimension, admissibility, Noetherianity or smallness condition is assumed.
The auxiliary comparisons work with a supplied topology alone, and the
final conjunction retains the exact topological-group quantifiers.

## Implemented proof

`repSubobjectOrderIso` compares the actual categorical subobjects of `A`
with those of its algebraic representation `A.obj`. It sends a monic
smooth intertwiner to its actual ambient intertwiner. The inclusion
preserves monomorphisms; fullness preserves and reflects the existence of
commuting factorizations. Every ambient subobject is recovered because a
subrepresentation of a smooth representation is smooth. Thus this is an
order isomorphism of actual categorical subobjects.

`moduleSubobjectOrderIso` composes that comparison with Mathlib's actual
representation/group-algebra equivalence
`Rep.equivalenceModuleMonoidAlgebra`, using `MonoOver.congr` and
`Subobject.lowerEquivalence`. Its target is the subobject order of
`ModuleCat.of R[G] A.representation.asModule`. Finally,
`groupAlgebraSubobjectOrderIso` composes it with
`ModuleCat.subobjectModule` to obtain the actual group-algebra submodule
order. The action is the existing `A.representation.asModule`, without an
assumed comparison or replacement action.

`renardFiniteType_iff` transports the unchanged source finite-type
predicate through `moduleSubobjectOrderIso`. An arbitrary subset of
subobjects is sent to its image; least upper bounds transfer in both
directions through the order isomorphism. The nonempty-chain, properness,
and top least-upper-bound conditions transfer as well. The proof then
applies the published unital-module comparison
`Langlands.Renard.ModuleFiniteType.finiteType_iff_finite` from
[RenardModuleFiniteTypeProof](../../CategoryTheory/RenardModuleFiniteTypeProof.md).

`renardFiniteLength_iff` transfers composition chains through
`groupAlgebraSubobjectOrderIso`. For a source chain, the published theorem
`Langlands.Renard.covBy_of_simple_cokernel` turns each actual simple
cokernel into a cover relation between successive subobjects. The order
isomorphism preserves these covers, producing a Mathlib composition
series of actual group-algebra submodules, with bottom and top endpoints
preserved. Conversely, a Mathlib composition series gives a strictly
increasing source chain, and
`Langlands.Renard.simple_cokernel_of_covBy` proves that every actual
successive categorical cokernel is simple. These bridge theorems are in
[SubobjectSimpleCokernel](../../CategoryTheory/Renard/SubobjectSimpleCokernel.md).
Mathlib's `isFiniteLength_iff_exists_compositionSeries` identifies the
result with the existing module finite-length predicate.
Length-zero chains transfer directly, so no nonzero case split is needed.

The final theorem combines the two comparisons under precisely the
quantifiers of the imported conjunction.

## Source correspondence and provenance

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The relevant original passages were read in full: III.1.4, final unnumbered
paragraph (printed page 60 / PDF66); A.I.2–A.I.3 (printed pages 248–249 /
PDF254–255); and A.VI.3 (printed pages 263–264 / PDF269–270).

This is a derived group-algebra proof of the published interface.
Renard transfers categorical terminology to smooth complex
representations of t.d. groups using the Hecke equivalence. The present
route proves the broader ring and group scope of the existing statement
using actual subobjects and the group-algebra action. The imported
finite-type predicate retains the statement's documented source repairs,
including nonempty chains of proper subobjects. The Hecke equivalence
and the III.1.4 irreducible-existence assertions remain separate results.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean
4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
