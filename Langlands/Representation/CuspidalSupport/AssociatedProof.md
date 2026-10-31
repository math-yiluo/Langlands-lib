# Weyl-transport filtration for associated cuspidal Levis

Authors: Workers 168 and 193.

`Langlands.CuspidalSupport.associatedJacquetFiltration.{uF,uV}` proves
the published `AssociatedJacquetFiltrationTheorem.{uF,uV} F T n`
for every prime `p`, actual `PadicField.{uF} p`, compatible topological
data `T`, and rank `n`, including zero. The field and inducing carrier
universes are independent. For every smooth quasicuspidal inducing
representation and associated pair of block Levis, the theorem proves
quasicuspidality of the actual normalized Jacquet-of-induction and supplies
its finite `ObjectRepFiltration`. Its graded indices are in bijection with
all `MinimalConjugatingPermutations`, and each actual graded representation
is equivalent to the corresponding whole-Levi Weyl transport.

The proof applies `associatedJacquetFiltration_of_prerequisites` and
discharges its three hypotheses with the published theorems
`Geometric.padicGeometricLemma`, `padicAssociatedGeometricPieces`, and
`ObjectRepFiltration.zeroFactorDeletionTheorem`. These are proofs of the
two geometric aggregates and the generic deletion proposition. The final
theorem has no extra premise.

At positive rank, `AssociatedAssembly` evaluates the geometric lemma's
natural filtration at the inducing representation. It composes the gluing
permutation with the exhaustive enumeration of minimal representatives,
so each graded isomorphism identifies the actual quotient with the
appropriate normalized geometric piece. For associated Levis and
quasicuspidal input, the associated-piece results make every nonconjugating
piece zero and identify every conjugating piece with whole-Levi transport.

Zero-factor deletion is applied to the predicate of conjugating the
entire Levi. Its retained-index bijection, followed by the restricted
minimal-representative enumeration, gives a bijection with all minimal
conjugating permutations. In particular, it retains conjugating factors
even when they are zero. Composing the deletion equivalence, evaluated
geometric isomorphism and piece-to-transport equivalence proves the
required equivalence for every actual graded quotient. Transport
quasicuspidality and invariance under representation equivalence make
these quotients quasicuspidal.

`AssociatedConditional` then applies the published
`isLeviQuasicuspidal_of_filtration` from `FiltrationQuasicuspidality`.
For each proper refinement, vanishing coinvariants of the graded
quotients imply vanishing coinvariants of the ambient representation.
This supplies the quasicuspidality conjunct using the same filtration.

At rank zero, `AssociatedRankZero` gives the direct argument. The Levi
groups are trivial, so quasicuspidality is vacuous. Evaluation at the
identity identifies smooth induction with the inducing carrier, and the
universal coinvariant lift inverts the trivial-group quotient. These give
an actual representation equivalence to transport. The one-step
filtration `0 ⊆ A` has its actual quotient equivalent to `A`, and its
single factor is indexed by the unique minimal conjugating permutation.
This factor is retained for the zero input as well.

The construction uses the exact normalized functors in the published
statement: induction has the positive half-modulus and Jacquet the inverse
half-modulus. The quotient carriers lie in `max uF uV`; representation
equivalences allow their universe to differ from the inducing carrier.
The theorem asserts a filtration, without a splitting, and applies to
arbitrary smooth quasicuspidal inputs without irreducibility,
admissibility, dimension or finite-length assumptions.

This is an internal final deduction for Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977),
Corollary 2.13(c), printed p.449/PDF10, using the geometric lemma in
section 2.12, printed p.448/PDF9. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original passages were read directly. The finite closure, deletion
and rank-zero arguments are internal algebra; the imported geometric
and piece proofs document their source correspondence. The target
already uses concrete minimal conjugating permutations, so this proof
does not require the separate Weyl-coset parametrization theorem.

Worker 193 supplied the rank-zero and conditional assembly helpers.
Worker 168 supplied the published finite-filtration closure proof,
verified the published prerequisites, and closed the unconditional
theorem. The published target pair and all previously published imported
pairs are unchanged.
