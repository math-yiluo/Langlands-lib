# Coefficientwise moderate growth from the joint structural target

`Langlands.Plancherel.RationalCoefficientModerateGrowthAssemblyStatement`
is an internal implication. Its two premises are the full propositions
`Langlands.GroupScheme.StandardCocharacterStatement` and
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`,
both at the field universe `u`. Its conclusion is precisely the existing,
unapplied `RationalCoefficientModerateGrowthStatement.{u,uV}`. The field
and representation-carrier universes remain independent.

The standard-cocharacter premise supplies integral standard directions and
the identification of the full standard Levi with the ambient group.
The joint existence premise supplies one common apartment, special vertex,
actual centralizer, special compact subgroup, standard-Levi Cartan comparison,
and simultaneous standard compact-open basis. Thus the compactness, Cartan
cover and coefficient estimates can all refer to the same subgroup.

The internal derivation first chooses a maximal split torus and a generic
cocharacter using the published existence theorem. Actual simple-root
finiteness needs no additional root-system premise. The joint witness's
standard-Levi comparison gives a finite centralizer lattice transversal.
Finite independent signed cocharacter charts then cover every rational
point between the same two compact outer sets, retaining the central lattice
directions. The finite-chart coefficient-growth implication gives the
conclusion in every supplied closed matrix embedding.

This statement does not assert either premise. Their existence and proof
obligations remain separate. In particular, proving this implication alone
does not prove the unconditional coefficientwise moderate-growth target.
It adds no finite-length, characteristic, splitness or rank restriction to
the conclusion. The statement has internal provenance: it records the
composition of structural and analytic interfaces rather than a new
transcription of Waldspurger's corollary.
