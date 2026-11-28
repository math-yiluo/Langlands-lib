# Radical and Levi coordinates of the ambient norm-one parabolic

The integration in Delorme's (7.7) uses the radical of \(P\) and the
points of its Levi whose images lie in \(G(\mathbb A)^1\). First,
`normOneParabolicImageEquiv` identifies the inverse image of
\(G(\mathbb A)^1\) in \(P(\mathbb A)\) with the parabolic image inside
\(G(\mathbb A)^1\). The group maps have the subgroup topologies from the
actual adelic point groups.

Every radical point maps into the ambient norm-one group because its
character logarithm vanishes by unipotence and functoriality. Applying
the full parabolic product decomposition, membership in the ambient
norm-one group then depends only on the Levi component. The resulting
Levi projection splits off the radical as its kernel.
`normOneParabolicCoordinates` applies the split-extension homeomorphism
to these restricted maps.

`normOneParabolicDensity` is the inverse Haar modulus of the
conjugation action on the radical. For a dynamic parabolic,
`normOneParabolicDensity_eq_inverseModulus` identifies this action
with conjugation by the same point in the ambient group. The adelic
parabolic modulus theorem identifies its modulus with the character
norm of the adjoint determinant. Its inverse is the negative modulus
parameter already used in the full Iwasawa integral. By the Haar
product theorem for radical-first order and Haar uniqueness,
`exists_normOneParabolicHaarProduct` fixes the radical Haar factor
and absorbs the required scalar in the ambient norm-one Levi Haar.

Finally, the Levi retraction and the Levi section preserve principal
points. The preimage of the principal parabolic under the radical
inclusion is precisely the principal radical, by rational point
lifting through the closed radical immersion.
`normOneParabolicFundamentalDomain` applies the strict fundamental
domain theorem for a split lattice. The product of the radical and
ambient norm-one Levi domains, carried through radical-first
multiplication, is a fundamental domain for the principal parabolic.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 23–24, (7.7).
