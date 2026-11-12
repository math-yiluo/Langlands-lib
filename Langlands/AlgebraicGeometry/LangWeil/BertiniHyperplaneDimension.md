# Dimension and generators for the generic hyperplane argument

Author: Worker 99.

This internal, derived module supplies the dimension and generator reductions
used by the proof of `BertiniGenericHyperplaneStatement`. It relies on published
Library results and Mathlib; it asserts no additional Bertini input.

`exists_algebraicIndependent_pair_of_two_le_ringKrullDim` extracts two entries of
a finite generating family of a domain of dimension at least two whose images
in its fraction field are algebraically independent over the base field.
The proof uses the published Noether-normalization helper
`P2MW.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime.P2mIrredHyp.exists_noether_two_le`
to bound the transcendence degree below by two. A transcendence basis contained
in the given generating family then has two distinct elements. Restricting to
these two elements and mapping into the fraction field proves the assertion.

`ringKrullDim_le_baseChange_reduction` preserves the lower dimension bound when
extending the base field to its algebraic closure and quotienting by the
nilradical. The coefficient extension is integral and injective, so the published
helper
`P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_eq_of_isIntegral_of_injective`
preserves dimension. Commuting the tensor factors gives the required base
change. Quotienting by the nilradical preserves the prime spectrum and hence
dimension. The theorem states the inequality needed by the generic hyperplane
proof.

`adjoin_range_baseChange_reduction` proves that the images of the original
generators still generate after these operations. Tensor generation follows
from Mathlib's `Algebra.TensorProduct.adjoin_one_tmul_image_eq_top`; applying the
surjective quotient algebra homomorphism gives generation of the reduction.

The statements and this proof organization are internal deductions for the
generic hyperplane proof, rather than assertions transcribed from literature.
The entry definition `dimensionAndGeneratorReductions` packages the three proved
reductions as a conjunction. It contains their proofs and introduces no
additional premise.
