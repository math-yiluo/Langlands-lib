# Fpqc descent and extensions for groups of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeFpqcExtension` proves
`Langlands.GroupScheme.MultiplicativeTypeFpqcExtensionStatement.{u}` for
every universe `u`. The two clauses give fpqc descent for affine fppf group
schemes and the extension property for an exact sequence of such groups
whose endpoints are of multiplicative type and whose middle residue fibres
are each connected or commutative. This is Corollary B.4.2 of Brian Conrad,
*Reductive group schemes* (2014), p. 299, with proof on pp. 300–301
(registered as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
See the [statement and source comparison](MultiplicativeTypeFpqcExtensionStatement.md).

The Lean proof applies `ExtensionReduction.fpqcExtension_of_threeStatements`
to `multiplicativeTypeFibralCriterion`,
`multiplicativeTypeCompleteLocalDeformation`, and
`multiplicativeTypeFieldExtension`. The assembly uses
`CompleteLocalDeformation.restrictMap_bijective` for the local character
comparison. See the [assembly proof](MultiplicativeTypeCoefficientExtension.md).

For descent, the base change reflects commutativity and geometric-fibre
multiplicative type. The comparison of positive torsion ranks under base
change and the quotient topology of the fpqc morphism transfer local
constancy to the base. The commutative branch of the fibral criterion
then gives multiplicative type.

For extensions, a common affine fppf cover diagonalizes both endpoints.
The field extension theorem gives multiplicative type on the middle
residue fibres. Connectedness of the middle fibre implies connectedness
of its surjective quotient, so the field theorem applies in that case as
well as in the commutative case. An exact finite coefficient model retains
the diagonalizable kernel and quotient, and field-extension reflection
gives multiplicative type at the contracted primes. At each such prime,
an étale residue-field splitting and complete-local deformation give
diagonalizability after completion. Fpqc descent to the ordinary local
ring followed by finite-presentation spreading gives an affine fppf
diagonalizing neighbourhood. Pulling back these neighbourhoods and
composing the covers gives the required fppf cover of the original base.
