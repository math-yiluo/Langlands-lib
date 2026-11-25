# Actual noetherian models and reduction to discrete valuation rings

This internal construction specializes the published finite
coefficient descent results to the prime subring of an affine base. It uses
the actual published scheme monicity, homomorphism and whole-group reductivity
descent proofs, with no additional descent premises.

`ReductiveMonomorphismDvrReduction.AffineModel f` contains an actual simultaneous
coefficient model of the specified homomorphism `f`. Its source and target
recovery isomorphisms and commuting square are part of that model. The additional
fields give noetherianity of its coefficient ring, source reductivity and scheme
monicity. The coefficient subalgebra is finitely generated over the prime
subring `⊥ : Subalgebra ℤ A`, whose carrier is in the same universe as `A`.
The target retains separatedness, local finite presentation and quasi-compactness;
it need not be affine.

`affineModel` chooses such a model. The prime subring is noetherian because it
is finitely generated over the integers. The actual reductivity extension and
homomorphism descent constructions, together with the published scheme monicity
descent proof, give a finite coefficient model. Its coefficient ring is noetherian by
the finite-type theorem. No canonical choice or uniqueness is asserted.

`AffineModel.isClosedImmersion` applies the locally noetherian case to the model
and uses the existing recovery lemma to transfer the closed immersion to the
original specified homomorphism. `affineCase_of_locallyNoetherianCase` uses the
chosen model. `generalCase_of_locallyNoetherianCase` then pulls the groups and
homomorphism back to each affine chart of the base. Reductivity, the three target
properties and scheme monicity survive base change. The published open-cover
locality lemma descends the resulting closed immersions.

`generalCase_of_dvrCase` composes this construction with the published valuative
reduction. `dvrCase_iff_generalCase` adds the converse by restricting the unchanged
arbitrary-base statement to spectra of DVRs. No DVR geometry or unconditional
closed-immersion theorem is proved here. The full direct-limit statement,
including its semisimple clauses, is not required.

The provenance is internal: the construction and deductions compose the existing
simultaneous coefficient model, actual reductivity descent, finite-type
noetherianity, recovery and open-cover lemmas, and the published DVR valuative
reduction.
