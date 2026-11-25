# The strict-Henselian fibral criterion from the clopen lift

This internal assembly reduces both branches of the multiplicative-type
fibral criterion over every strictly Henselian local ring to the single
explicit premise `MultiplicativeTypeStrictHenselianLiftStatement`.
It imports the torsion-determination proof and field comparisons.
It supplies no proof of the clopen-lifting premise.

`FibralDiagonalization H` retains a finitely generated abelian character
group and an actual isomorphism `H ≅ D_A(M)`. The character group may have
torsion. The choices are noncomputable, with no uniqueness or naturality
claim.

For an affine flat locally finitely presented group `H` over a strictly
Henselian local ring `A`, `connectedSplitting` constructs this data when all
residue-field fibres are connected and all geometric fibres have
multiplicative type. `commutativeSplitting` constructs it when `H` is
commutative, all geometric fibres have multiplicative type, and each
positive geometric torsion coordinate-order function is locally constant.
The base need not be Noetherian, complete or reduced, and the group need
not be smooth.

Both constructions first obtain the required special-fibre diagonalization
from the closed geometric-fibre hypothesis using
`LocalSpecialGeometricFiber.specialFiberDiagonalization`. They then apply
the two conditional local diagonalization constructions. The commutative
case supplies the theorem
`multiplicativeTypeTorsionDetermination` internally.

`connectedCriterion` and `commutativeCriterion` give the complete
equivalences over `Spec A`, conditional only on the clopen-lifting premise.
Their forward implications use the relative-to-geometric-field
comparison and the exact geometric torsion coordinate-dimension
local-constancy theorem. Their reverse implications use the actual
diagonalizations just constructed. Their fibre predicates and torsion
functions are precisely those of the full fibral criterion.

This assembly removes the need to supply a character group,
special-fibre isomorphism or torsion-determination proposition as further
inputs. It retains the explicit lifting premise and the restriction to a
strictly Henselian local base. General-base detection/spreading and the
proof of the lifting premise are not part of this module; the Library
proves the lifting premise as `multiplicativeTypeStrictHenselianLift` in
`MultiplicativeTypeStrictHenselianLiftProof`. The provenance
is internal composition of the named actual constructions and Library
theorems.
