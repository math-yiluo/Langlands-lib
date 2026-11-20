# The local component on the full cuspidal carrier

`CuspidalSpectralPresentation.localMultiplicityEquiv` compares the actual
cuspidal carrier restricted to the general linear group at one finite place
with the actual local component tensored with a trivial multiplicity space.
It uses the supplied irreducible admissible finite spectral components.

The spectral tensor equivalence identifies the restricted tensor of the supplied
finite factors with the finite factor chosen inside the whole cuspidal carrier.
Evaluation of its intertwiners gives the full cuspidal carrier. Expose the selected
finite factor in the restricted tensor and identify it with the actual local
component of the presentation. The remaining finite factors and the multiplicity
space of the finite factor go into the trivial tensor factor. On pure tensors,
the claimed equivariance follows by acting on the selected factor and then applying
the finite spectral equivalence and the evaluating intertwiner.

This is a derived local restriction of the tensor description used in Langlands,
*On the notion of an automorphic representation*, Corvallis Part I (1979),
printed pp. 203 and 205 (PDF pp. 198 and 200), source
`langlands-1979-notion-automorphic-representation`. The map is used to construct
local coefficient projections for the normalized cuspidal induction in Task 6823.
