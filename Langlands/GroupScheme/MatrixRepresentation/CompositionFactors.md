# Finite simple factors and their common unipotent matrix kernel

This internal construction develops the composition-factor step in KP
Lemma 2.2.11 (printed pp.72–73, PDF pp.103–104, *Bruhat–Tits theory: a new
approach*, 2023). No complete reducibility is assumed.

For an affine group, `Intertwines.pointMatrix` transports the existing
all-affine-tests intertwining identity to every scheme test. It checks an
affine model of the group, converts its matrices to sections, and pulls that
identity back along each test point.

`pow_sub_one_eq_zero_of_split_exact` is a matrix calculation over a field
followed by any homomorphism to a commutative ring. In split exact coordinates
`B,C,Q,D`, identity action on the subspace and nilpotent deviation of exponent
`l` on the quotient force nilpotent deviation of exponent `l+1` on the ambient
space. The projection `P=1-DQ` has image in `ker Q = range B`, so `BCP=P`.
Writing `A=M-1`, identity action gives `AB=0` and hence `AP=0`. Thus `A=ADQ`.
The quotient intertwiner gives `QA^l=(N-1)^l Q=0`, and consequently
`A^(l+1)=ADQA^l=0`.

`SimpleFactorFamily ρ τ` records a finite family of actual simple
subquotients of `ρ`, with the property that their common kernel acts
unipotently on `τ` on every scheme test. Simplicity is expressed by a
nontrivial vector space and the all-test stable-subspace alternative, matching
the actual irreducibility interface.

`nonempty_simpleFactorFamily_of_quotient` constructs these families by strong
induction on the dimension of an actual quotient `τ` of `ρ`. In positive
dimension, choose an actual simple subrepresentation of `τ`, then pass to the
quotient by its image. Rank–nullity and the nonzero simple subspace make the
quotient dimension strictly smaller. The simple inclusion and the supplied
surjection from `ρ` express the new factor as an actual subquotient of `ρ`.
The inductive call uses the composite surjection from `ρ`, so it does not
assume transitivity of an unspecified subquotient relation. Prepending the
new factor and applying the split exact matrix calculation establish the
common-kernel assertion. In dimension zero the family is empty and the matrix
ring is a singleton.

`nonempty_simpleFactorFamily` starts with the identity quotient;
`simpleFactorFamily` chooses one such family. All fields and characteristics
are included, as is zero ambient dimension. The construction proves
unipotence of the matrices on a common kernel on every test. It does not yet
prove that this kernel is a finite group scheme, or prove spectral boundedness.
