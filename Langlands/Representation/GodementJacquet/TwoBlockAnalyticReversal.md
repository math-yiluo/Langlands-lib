# Canonical analytic inputs for reversed inverse-transpose blocks

This derived prerequisite provides canonical p-adic adapters for the actual
ordered-family transport in `InverseTransposeProductAnalytics`. It does not
prove convergence or product-integral expansion for an induced representation.
The statements work for any finite list of positive ranks, in particular the
two blocks in the analytic-induction target, with independent field and carrier
universes.

`reversedInverseTransposeBlocks m σ` is the actual representation family
`i ↦ (σ i.rev).comp inverseTranspose`, on the complete dependent carrier family
`i ↦ V i.rev`. Its block ranks are `m i.rev + 1`. The finite reindexing lemma
`sum_reversedSuccBlocks` proves that their total rank is unchanged.

`GeneralLinear.inverseTranspose_scalar` is proved from the actual matrix
entries and inversion of the scalar inclusion. Consequently,
`Classification.hasGLCentralCharacter_comp_inverseTranspose` transports a
specified whole-carrier scalar central action to the inverse character. This
is a direct equality of actions and does not require irreducibility or a
contragredient identification. For a continuous quasicharacter its inverse is
again a continuous quasicharacter by the existing group structure.

`isAdmissible_reversedInverseTransposeBlocks` applies the published
admissibility transport under a continuous group equivalence to each actual
inverse-transpose automorphism. The carriers and their complex-module
structures remain the originals, in reversed order.

`Padic.matrixAnalyticAssertions_reversedInverseTransposeBlocks` applies the
published coefficient-pullback equivalence to each block. Thus each supplied
transformed block analytic assertion gives the ordinary assertion for its
reversed pullback block, with the same polynomial and canonical group Haar
measure for that block rank.

`Padic.iotaMatrixAnalyticAssertions_succBlocks_iff` specializes the published
actual representation transport to the positive-rank family
`RankinSelberg.succBlockShape m h`. Its reversed shape is definitionally the
successor-block shape of `i ↦ m i.rev`, up to proof irrelevance for the sum
witness. The proof uses the full upper-to-opposite-to-reversed-upper normalized
induction equivalence in `InverseTransposeProductAnalytics`, then reindexes
the polynomial product using `Fin.revPerm`. Polynomial commutativity alone is
not used to identify representations. Common convergence bounds, all actual
coefficient functions and full-matrix tests, rational-continuation denominator
guards, the entire Laurent value module and its normalized generator all pass
through the published analytic equivalence unchanged.

No Fourier transform or additive measure is changed or constructed here. No
functional-equation data for the reversed family is asserted: the result uses
only the transformed analytic assertions of its original blocks. The
noncompact ordinary analytic-induction theorem is still required to obtain the
induced analytic conclusion. All provenance is internal, from the published
actual matrix maps, coefficient transport, normalized induction transport,
admissibility transport and finite reindexing identities.

The local canonical topology, valuation, local-field and group measurable
instances have explicit `twoBlockReversal` names. This preserves their terms
and locality while avoiding generated-declaration name collisions when this
module is imported together with the rank-one matrix Weyl comparison.
