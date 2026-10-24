# Pure algebraic semisimplicity of intrinsic isotypic sums

This module defines the internal proposition
`Langlands.CompactCoefficientClass.IsotypicSemisimplicityTheorem`.
It supplies a statement for a subsequent proof, with no theorem proving it.

## Exact statement

For every group `G : Type uG` equipped with a `TopologicalSpace`, and every
actual smooth complex representation `A : SmoothRep.{0, uG, uV} ℂ G`, the
proposition asserts the conjunction of the following three conclusions:

1. For every `c : CompactCoefficientClass.{uG, uC} G`,
   `(isotypicSubrepresentation c A).toRepresentation` is semisimple.
2. For every `t : Finset (CompactCoefficientClass.{uG, uC} G)`,
   `(selectedIsotypicSubrepresentation t A).toRepresentation` is semisimple.
3. `(totalIsotypicSubrepresentation.{uG, uC} A).toRepresentation` is
   semisimple.

In each clause, semisimplicity means Mathlib's
`Representation.IsSemisimpleRepresentation`: the lattice of invariant
subspaces of that representation is complemented. Mathlib identifies this
condition with semisimplicity of its associated complex monoid-algebra module.
The complements in this condition are internal to the displayed
subrepresentation; this statement does not assert that it has a complement
inside `A`.

The universes `uG`, `uC`, and `uV` are independent. Representatives of a class
have carriers in `Type uC`, while the ambient carrier lies in `Type uV`.
The total sum explicitly retains `uC`, even though that universe does not
occur in its argument `A`. No comparison of sums across different
representative universes is asserted.

## Existing constructions and internal provenance

The proposition uses the published constructions unchanged:

- [Isotypic](Isotypic.md) defines the single-class sum as the supremum of the
  ranges of all intertwiners from all representatives of that class into `A`,
  and the total sum as the supremum over all classes at the fixed `uC`.
- [SelectedProjector](SelectedProjector.md) defines the selected sum as the
  supremum of the single-class sums indexed by the subtype of a finite set.
  This definition requires no complementarity hypothesis, even though the
  projector constructions in that module do.
- [Classes](Classes.md) supplies the classes of actual irreducible smooth
  complex representations with compact smooth-dual coefficients.

The provenance is an internal algebraic consequence suggested by these
definitions, not a transcription of an analytic decomposition theorem.
An intertwiner from an irreducible representation has zero or simple image,
and sums of simple submodules are semisimple. Thus compact coefficients
determine which irreducible classes are indexed, whereas irreducibility and
the range-and-supremum construction provide the algebraic reason for the
expected conclusion.

For a later proof, Mathlib's `RingTheory.SimpleModule.Basic` supplies
`IsSemisimpleModule.range`,
`isSemisimpleModule_biSup_of_isSemisimpleModule_submodule`, and
`isSemisimpleModule_of_isSemisimpleModule_submodule'`.
`RepresentationTheory.Semisimple` supplies
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`,
and `Subrepresentation.subrepresentationSubmoduleOrderIso` relates invariant
subspaces to monoid-algebra submodules. A proof using these results must
establish the required transfers for the actual range and subrepresentation
carriers. This module implements none of those proof steps.

## Scope

The only group structures quantified in the proposition are `Group G` and
`TopologicalSpace G`. Smoothness of `A` and the coefficient property of the
indexed classes are inherited from the existing types. There is no
topological-group, separation, local-compactness, total-disconnectedness,
compact-open-cofinality, Haar-measure, admissibility, finite-dimension,
finite-length, or ambient-semisimplicity premise. In particular, no intrinsic
complement, projector, or desired conclusion is assumed.

The finite selection may be empty, in which case its sum is zero; the
statement imposes no nonzero condition. The total sum need not equal `A`.
The proposition makes no claim of compact coefficients for the sums, no
identification with an analytic projector, and no final block-isolation
assertion.

Worker 199 wrote this statement and documentation from Worker 319's
specification. Existing Library pairs are imported without modification.
