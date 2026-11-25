# Prescribed clopen diagonalizable lifts over strictly Henselian local rings

The theorem
`Langlands.GroupScheme.multiplicativeTypeStrictHenselianLift` proves exactly
`MultiplicativeTypeStrictHenselianLiftStatement` in every
universe. For any permitted strictly Henselian local base, ambient group,
finitely generated full abelian character group and prescribed
special-fibre isomorphism, it supplies a group homomorphism with exactly
that special-fibre map and both open and closed immersion properties.

The proof applies
`StrictHenselianLiftReduction.multiplicativeTypeStrictHenselianLift_of_completeLocalDeformation`
to the complete-local deformation theorem
`multiplicativeTypeCompleteLocalDeformation`. The reduction chooses a
Noetherian local coefficient model over a prime localization of a
finite-type integer algebra, with split special fibre and an actual local
map into the original Henselian ring. It lifts a chosen diagonalization
to the completion, uses order-one étale approximation to realize the
homomorphism over an étale algebra, and lifts the residue point into the
original ring by Henselianity. A Noetherian local special-fibre criterion
proves the lift clopen before transfer to the possibly non-Noetherian
base. Local Hom comparison between diagonalizable groups then adjusts the
source so that the prescribed special-fibre map is recovered exactly.

The construction adapts the clopen lifting step in Brian Conrad,
*Reductive group schemes* (2014), proof of Theorem B.4.1, pp. 298–299.
It allows non-Noetherian bases, nonsmooth and noncommutative ambient
groups, and character groups with torsion. The statement
includes the hypothesis that all geometric fibres have multiplicative
type. The argument uses the prescribed special-fibre diagonalization to
supply the splitting it needs.
