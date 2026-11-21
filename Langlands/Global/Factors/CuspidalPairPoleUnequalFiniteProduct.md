# Prescribed finite factors of the ordinary unequal-rank Whittaker product

The ordinary padded Whittaker product of two actual cuspidal tensor
vectors separates the finite Whittaker functions at every place in
`S`. The two remaining terms are the Whittaker functions of the
vectors with the reference finite components, evaluated on the
infinite coordinates. Their infinite tensors are the ones supplied
for the original vectors.

On the ordinary partial domain, the retained-coordinate reduction
removes all away coordinates. Padding the retained point commutes
with the product of its infinite part and its finite translation
supported on `S`. The finite separation theorem applies to the
larger group with that padded translation. For the smaller group it
applies to the inverse character with its canonical finite
components. The given coefficient identities realize the two
Whittaker functions at each finite place. Multiplication gives the
paired product with scalar one.

The finite tensor separation in the ordinary Eulerian integral is
part of J. W. Cogdell, *Analytic theory of L-functions for GL_n*
(2004), §4.1, printed pp. 219–220 (PDF pp. 222–223). The Lean proof
uses the actual finite tensor realization and the Library's
retained-coordinate reduction. The two infinite terms are left as
functions of the joint infinite coordinates.
