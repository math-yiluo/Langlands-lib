# Semisimple root data from actual integral reflection data

This internal reduction supports the semisimple-perfectness proof. It retains
an arbitrary field `k : Type u`, including imperfect fields and positive
characteristic. It constructs a root datum and proves finite coroot index
from explicitly supplied `RelativeRootReflectionData`. It does not construct
those reflection data or prove semisimple perfectness.

Let `G` be an actual semisimple group scheme and `i : T → G` the closed
inclusion of a split commutative torus. No maximality hypothesis is needed.
The actual roots are the nonzero adjoint weights in the published
`relativeRoots i`; the lattices and their pairing are the published actual
character and cocharacter lattices of `T`.

`IsSemisimple.cocharacter_eq_zero_of_annihilates_relativeRoots` proves that an
integral cocharacter pairing to zero with every actual root is zero. The
published `rootAnnihilatorCentrality` makes its composite with `i` central.
The represented finite scheme-theoretic centre then supplies a factorization
of this composite and of the zero cocharacter through a finite group scheme.
The published `finiteHom_cancel`, applied to the structural map of that finite
group scheme, equates these two maps from the smooth connected group `Gm`.
The monomorphism underlying the closed torus inclusion cancels `i`, yielding
equality of the original cocharacters. This is the finite-centre argument of
`IsSemisimple.finite_quotient_rootSpan`, isolated before choosing a root datum.

`IsSemisimple.relativeRootSpan_eq_top` proves that the actual roots span the
whole rational character space, without assuming a root datum. Smoothness of
the semisimple group gives finiteness of the actual roots. The published
`IsSplitTorus.toRat_mem_ratSpan_iff_annihilator` detects membership of each
rationalized integral character by its pairings with all integral common
annihilators. The preceding result makes each such annihilator zero. Tensor
induction then extends membership from these integral generators to every
element of the rationalized character lattice.

For explicit actual integral reflection data `D`,
`RelativeRootReflectionData.exists_semisimple_rootDatum` uses this spanning
result to supply the joint spanning premise of the published
`RelativeRootReflectionData.rootDatum` construction. It obtains a finite
Mathlib root datum on the actual integral lattices, with the exact
`latticePairing T`, actual roots, and actual normalizing points realizing
every reflection, as required by the full `IsRootDatumOf`. The published
`IsSemisimple.finite_quotient_rootSpan` supplies finite root index, and
`RootPairing.finite_quotient_rootSpan_iff_corootSpan` supplies finite coroot
index. No reducedness conclusion is asserted.

`SemisimpleReflectionDatumStatement` is the Prop-valued universal formulation
of this construction. Its proof, `semisimpleReflectionDatum`, applies the
preceding construction. Semisimplicity supplies the affine instance and the
closed inclusion supplies the monomorphism needed to state the reflection
data. These instances add no further geometric hypotheses.

The provenance is internal: this module composes the named published
centrality, finite-map cancellation, integral-span detection and conditional
root-datum assembly results. It specializes the latter assembly to
semisimple groups, where the actual roots alone already span rationally.
Root-reducedness and the general character-complement theorem are therefore
unnecessary inputs for this conditional construction. The existence of
actual integral normalizer reflection data remains a structural prerequisite,
as does the subsequent generation argument for the semisimple-perfectness
target.
