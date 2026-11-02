# The invariant counit under detection of zero comodules

Authors: Worker 101 and Worker 1203.

This internal algebraic step concerns the canonical `B`-linear map
`invariantCounit θ : B ⊗[A] θ.invariantSubmodule → M`,
where `A = invariantRing t`. It assumes `RingEtaleEquivalenceRelation t`,
acyclicity of every coaction in the chosen module universe, and the explicit
additional hypothesis that a coaction with a subsingleton invariant module
has a subsingleton underlying module. This last hypothesis is called
`hdetect` in Lean. The ring universe is `u` and the module universe is
`max u v`; kernels, quotients, invariant modules, and scalar extensions
therefore remain in the universe covered by both hypotheses.

For injectivity, the implemented proof equips the kernel of the counit
with its kernel coaction. An invariant element in that kernel maps to an
invariant element of the induced coaction that the counit kills. The
counit's map on invariants is injective because the unit is surjective,
and the all-module unit theorem supplies this surjectivity from
acyclicity. Consequently the kernel's invariant module is subsingleton,
and `hdetect` makes the kernel itself subsingleton. This proves
`invariantCounit_injective_of_acyclic_of_detects_zero`.

For surjectivity, the proof equips the cokernel with its quotient
coaction. Acyclicity lifts each invariant in the cokernel to an invariant
in `M`. The always-surjective map on invariants of the counit then lifts
that invariant to an invariant in its domain. Its composite with the
quotient map vanishes, so the cokernel has a subsingleton invariant
module. Applying `hdetect` makes the entire cokernel subsingleton.
The quotient criterion for membership in the counit's range proves
`invariantCounit_surjective_of_acyclic_of_detects_zero`.

The bijectivity lemma combines these results.
`invariantCounitLinearEquiv` packages the actual counit as a `B`-linear
equivalence, and its application lemma records the underlying map.

The provenance is a direct internal derivation from the unchanged
published coaction and acyclicity predicates, the kernel and cokernel
constructions, the counit identities, and the all-module invariant unit
theorem. Worker 1203 supplied the induced coaction and unit argument on
which the injectivity proof depends. No original-literature theorem is
asserted here. In particular, this module does not prove `hdetect` from
Noetherianity and acyclicity, nor does it prove the full Serre criterion
or assume an affine quotient or descent conclusion.
