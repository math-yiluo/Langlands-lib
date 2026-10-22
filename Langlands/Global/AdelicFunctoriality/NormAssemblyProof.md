# Proof of the norm assembly reductions

`normAssembly` proves the exact proposition `NormAssembly.{u, v}` in
`NormAssemblyStatement.lean`, preserving both independent universe
parameters. The proposition is a conjunction of two implications. Its
proof does not prove either arithmetic premise or supply an unconditional
idele-class norm.

For the first implication, the proof uses
`principalNormCompatibility_of_completedTensorComparison` from
`NormReduction.lean`. That module proves compatibility of the determinant
norm with scalar extension by comparing matrices of left multiplication.
It proves compatibility with binary products by the block determinant
formula and with arbitrary finite dependent products by finite-type
induction. Applying these identities to the actual completed tensor
equivalences gives the principal formula at each place. The infinite
comparison is already proved in `Norm.lean`; the finite comparison is
obtained from the explicit hypothesis `CompletedTensorComparison`.
Extensionality of the product and restricted product gives equality of
the full principal adeles.

For the second implication, `ideleClassNormDescent` takes the explicit
principal compatibility hypothesis and fixes the two actual number
fields and their algebra structure. The constructed witness is
`ideleClassNormOfPrincipalFormula` from `NormDescentReduction.lean`.
That module lifts the given adele identity to equality of units, with
field-unit norm `Units.map (Algebra.norm K)`, and proves preservation of
the principal subgroups. `QuotientGroup.map` therefore defines the
homomorphism on the actual idele-class groups. The quotient topology
proves continuity from continuity of the raw `ideleNorm`.

The representative formula follows directly from the definition of this
quotient map. Its uniqueness is
`ideleClassNormOfPrincipalFormula_unique`, proved by quotient induction.
The final theorem combines this implication with the determinant
reduction. It introduces no choice of arbitrary norm or comparison
equivalence: all maps are the ones constructed in `Norm.lean`.

The paired Markdown for `NormReduction.lean` and
`NormDescentReduction.lean` describes these helper proofs in detail and
records their arithmetic provenance. The implemented determinant route
is the base-change and product argument underlying Weil, *Basic Number
Theory*, second edition (1973), Chapter III section 3, pp. 53-54, and
Chapter III section 4, Theorem 4 and Corollary 3, pp. 56-58. The descent
uses the actual principal quotient and idele topology discussed in
Chapter IV sections 3-4, pp. 71-76. The exact conjunction is the project's
derived organization of these reductions.

The outstanding task remains the unconditional completed tensor
comparison at finite places. Once it is proved, the first implication
supplies `PrincipalNormCompatibility`; the second supplies the unique
continuous quotient map. Publishing these implications alone does not
complete the full action and norm task.
