# The classical maximal-torus argument for full-kernel centralizers

Author: Worker 1465.

This internal unit assembles the actual split maximal-torus factorization,
full character-kernel centralizer containment, identity-component factorization,
and rootwise radical detection over an algebraically closed field. The character
kernel and centralizer retain their meanings on all scheme tests. The character
need not be primitive. This unit does not yet supply the arbitrary-field descent.

`range_le_kernelCentralizer_of_torus_factor` uses commutativity in the containing
torus. `torusCentralizer_eq_range_of_comp_mono` reflects equality with the torus
range through a monic intermediate subgroup. `kernelCentralizerTorusFactor`
factors the containing split torus first through the supplied centralizer
representative, then through its actual identity component. Its composite with
the two inclusions is the original torus morphism.

`exists_factor_split_maximalTorus` applies the published split-torus image
factorization and maximal split-torus extension, then finite Galois splitting
over the algebraically closed field to upgrade maximality.

The final reductivity theorem applies the published rootwise radical-detection
criterion in the actual identity component. Its torus is self-centralizing by
monic comparison with the ambient maximal torus. Every root restricts to an
integer multiple of the original character by the integral-weight support
lemma. The corresponding ambient proportional-root centralizer is connected
reductive by the published dynamic-centralizer theorem, and its entire range
lies in the full-kernel centralizer. Connectedness factors it through the
identity component. Restriction of this actual representative supplies the
radical-free witnesses for the criterion. The provenance is internal composition
of these published and accompanying constructions.
