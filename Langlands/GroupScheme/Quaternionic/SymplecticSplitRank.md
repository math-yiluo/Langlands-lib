# Split rank one for antihermitian forms of rank two or three

This internal development combines the weighted diagonal nontriviality detector
with the hyperbolic basis and actual symplectic cocharacter constructions in
`HyperbolicBasis`, `SymplecticCocharacter` and `SymplecticPoints`.

Over any infinite field `K`, let `D` be a finite-dimensional central division
`K`-algebra and let `σ` be an involution of the first kind. A nondegenerate
trace-valued antihermitian form of rank two or three and Witt index one has
a reduced-norm-one isometry group of split rank one. No characteristic,
quaternion-dimension or symmetric-subspace-dimension restriction is required.

The pair-weight cocharacter is nonzero because its composite with the actual
ambient inclusion is the weighted diagonal cocharacter, whose weight at the
first distinguished coordinate is one. For `gramTwo D` and `gramThree c`,
the support condition follows by checking the finitely many matrix entries.
The hyperbolic basis results identify an arbitrary form with one of these
normal forms, and `symplecticGroupCongr` transports the cocharacter to the
original form. Its nonzeroness is preserved by the inverse isomorphism.
The published rank-one criterion then combines this lower bound with the
Witt-index upper bound.

This is an internal consequence of the named constructions and criteria.
The final local theorem still needs the standard symplectic structure theorem
for simple connectedness and almost simplicity.
