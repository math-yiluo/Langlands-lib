# Full Weyl-image finiteness from representation weight stability

This internal supporting construction combines the published weight matrices
and their generation theorem in `Rational.CharacterRestrictionFiniteIndex`
with `GroupTheory.FiniteGeneratorAction`. It retains preservation of nonzero
weight matrices by normalizing points as an explicit premise.

For a standard split torus indexed by a finite type over any field,
`exponentAut` writes the actual inverse-precomposition character action of a
torus automorphism in the published integer exponent coordinates. The lemma
`characterLatticeEquiv_symm_exponentAut` identifies this coordinate action
with the actual action on algebraic characters.

For a finite-dimensional matrix representation of the ambient group,
`weightCharacters` is the set of algebraic characters corresponding to
nonzero weight matrices. It includes the zero character when its weight
matrix is nonzero. The finite monomial support of the universal matrix
contains all such exponents, so this set is finite. If the composite of
the torus embedding and the representation is a monomorphism of schemes,
`closure_weights_eq_top` makes these exponents generate the entire exponent
group. Transporting this equality along the actual character equivalence
shows that `weightCharacters` generates the entire integral character group.

The conditional theorem `finite_weylImage_of_weight_stable` takes precisely
preservation of nonzero weight matrices under `exponentAut` of each chosen
`normalizingAut`, together with the composite monomorphism. The coordinate
comparison turns that premise into preservation of `weightCharacters` by
the actual Weyl action. The generic finite-generator theorem then proves
finiteness of the full Weyl-action image. It controls the entire character
group, including directions outside the root span.

The argument permits arbitrary characteristic and field universe, a torus
of rank zero, and a representation of dimension zero. It assumes neither
centrality of the torus nor smoothness, reductivity or connectedness of the
ambient group. The support-stability premise remains a separate obligation;
this module does not claim unconditional Weyl-image finiteness or the final
central-isogeny root-datum theorem.
