# Transition maps from cocycle representatives of a Hodge summand

Suppose \(X\) is smooth and separated over \(\operatorname{Spec}R\) with
a finite affine cover \(U\) and a finite free frame of relative one-forms.
For a family of total cocycle representatives supplied by
`HodgeSummandCocycles`, their function components \(a_{k,ij}\) belong to
the extension of the base ideal \(I\) on every pair intersection.

On an affine open \(W\subseteq U_i\cap U_j\),
`overlapContraction` sends the \(k\)-th frame vector to
\(a_{k,ij}|_W\) and extends linearly over \(\Gamma(X,W)\).
The contractions take values in the extended ideal. Their restriction
formula follows by expanding a form in the frame and restricting each
coefficient and frame vector. On a common affine open of three charts,
the function cocycle identity gives \(C_{ij}+C_{jl}=C_{il}\). In
particular \(C_{ii}=0\).

When \(I^2=0\), the algebra map `transition` adds the derivation \(C_{ij}d\)
to the identity. The contraction formulas show that the resulting
algebra maps commute with restrictions, compose on common affine opens
of three charts, and are the identity for two equal chart indices.
If the original closed forms are the frame vectors, the contractions
take the form components of the representatives on each pair to their
overlap functions. Indeed the perturbation lies in the ideal times the
one-forms, which the contractions annihilate. The cocycle equation for
the form components says their Čech difference equals the differential
of the overlap function. The closed-form coordinate change therefore
pulls the first form back to the second.

The transition construction uses square-zero gluing in Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, revised
14 March 2021, §2.1.3. Taking the overlap functions from the total
cocycles gives transitions for the lifted summand of Proposition
2.1.6.8. The retained source is
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
