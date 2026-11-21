# Lifting layer bases to a splitting basis

This is an internal tool for the cyclic lift in the proof of Bushnell–Kutzko (1993), (2.4.1)(iii). The underlying layer-basis construction is the one used in §2.5. It is implemented for a lattice chain over the integers of a nonarchimedean local field.

A nonzero finite coefficient family has a minimum uniformizer valuation. After factoring it out, the coefficients are integral and at least one has nonzero residue. For a linear combination of the proposed basis vectors with these normalized coefficients, take the first layer with a nonzero residual coefficient. All other terms vanish in that layer and the sum in that layer is nonzero by independence. This proves linear independence over the local field, and, with the common uniformizer factor restored, proves the splitting property.

For spanning, a coset modulo the span of the proposed basis has a representative of largest depth if the coset is nonzero. Scale that representative into one period, subtract a combination lifting its coordinates in the corresponding layer, and scale back. This increases depth within the same coset, a contradiction.

The final filtration test uses the splitting property to check an endomorphism's filtration degree on individual basis vectors at their exact depths. The coset argument and this filtration test are derived implementation lemmas rather than separate claims from the source.
