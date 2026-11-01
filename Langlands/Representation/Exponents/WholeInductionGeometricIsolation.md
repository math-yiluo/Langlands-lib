# Whole-induction isolation from actual geometry and finite generation

Author: Worker 526, using the central-block and source-twist design of
Workers 430 and 359. The namespace is
`Langlands.WholeInductionGeometricIsolation`. This internal assembly uses
the actual leading opposite filtration, irreducible opposite-Jacquet
embedding and generalized-central retraction constructions.

`wholeRetractionOfGeometricInputs` takes the upper geometric lemma for
`B` and `B.reverse`, the exact leading-piece exclusion statement, and
finite generation of the actual twisted normalized whole induction.
For an irreducible analytically tempered coarse input and strictly
decreasing coarse vector, it constructs actual maps from the coarse
twist into the opposite Jacquet module of its induction and back. Their
composite is identity on the source, and their reverse composite fixes
every full generalized central-character space with real part `size * t`.
One pair of maps serves every such character, without an open-kernel
condition in this stronger helper conclusion.

For one existing Borel Haar measure on the actual full central quotient,
analytic temperedness supplies admissibility and a unitary full central
character `c` acting on the original representation. Multiplying `c` by
the actual determinant twist restricted to the full centre gives the
scalar character `chi0` of the coarse twist. Unitarity and the actual
block-scalar formula give real part `size k * t k`.

The supplied upper geometric lemma constructs the actual finite opposite
filtration through `LeadingOppositeFiltration`. Its identity grade is
equivalent to the coarse twist. The public same-character restriction
and reversal adapter, with the supplied actual leading-piece exclusion,
show that all other grades exclude every full central character with
this leading real part. This step preserves the full character and its
uniform generalized nilpotence, rather than only its real coordinate.

`irreducibleOppositeJacquetUnit` supplies an injective embedding of the
irreducible admissible coarse twist. It is nonzero because that carrier
is nontrivial. Admissibility of induction and its supplied finite
generation imply finite full-central operator span on the actual
opposite Jacquet module, by `oppositeJacquetCentralAction`.
`FilteredCentralRetraction.retractionOfIsolatedGrade` then identifies
the entire selected generalized block, projects onto it and constructs
the required map back. Character uniqueness at the identity grade makes
the same maps fix every qualifying generalized space.

All modules and maps retain their actual quotient, right-translation
induction and opposite normalization. No semisimplicity, chosen
splitting, support map or representation-carrier dimension premise is
assumed. The exact comparison entry module supplies the three helper
inputs by the public geometric and exclusion proofs and the proved
finite-length induction adapter.
