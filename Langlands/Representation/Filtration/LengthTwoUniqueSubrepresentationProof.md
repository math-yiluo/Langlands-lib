# Proof of the length-two unique-subrepresentation criterion

Author: Worker 163. The target statement is independently accepted and
published in the Library. This pair proves that exact target with no added
outer hypotheses.

This proves the derived criterion
`Langlands.LengthTwoUniqueSubrepresentationCriterion` using the strict-count
and actual filtration lemmas in `Filtration.LengthTwoMatching`. It has no
p-adic, derivative, segment or classification input.

Every nonzero proper invariant subspace has count one: positivity gives a
positive count, and its strict inclusion into the whole representation bounds
its count strictly below two. The nonzero map excludes the zero
representation. Thus failure of irreducibility gives an actual nonzero proper
subspace. The annihilation premise places each such subspace in the kernel of
the given map. That kernel is nonzero because it contains a nonzero subspace,
and proper because the map is nonzero. It too has count one. Strict
monotonicity rules out strict containment between these count-one subspaces,
so each is exactly the kernel. This gives uniqueness as an invariant subspace.

For any nonzero proper `S`, the count bounds make `0 ⊂ S` and `S ⊂ A` covering
pairs. The published `twoStep_hasSimpleFactors` constructs the actual
length-two series. To identify its factors with the actual smooth objects,
the proof uses `MultiplicityAdditivityProof.two_step_equivs` on the canonical
inclusion `S → A` and quotient `A → A / S`. Their actual linear maps form a
short exact sequence, and the inclusion's range is exactly `S`. The resulting
representation equivalences transfer irreducibility of the two graded pieces
to `SmoothRep.subrepresentation A S` and `SmoothRep.quotient A S`.

The closed theorem quantifies the four independent universes of the statement
and introduces exactly its hypotheses. All hypotheses must be proved by a
later application to normalized induction; this algebraic theorem alone does
not prove the two-supercuspidal product structure or its ordered Jacquet
identifications. The statement Markdown explains the derived BZ77 provenance.


## Provenance and independence

This is the internal algebraic criterion isolated from the count-one kernel
argument in Bernstein–Zelevinsky (1977), section 2.16(1), printed pp.449–450
(PDF pp.10–11), with the count discussion in section 2.14. The registered
original is `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The implemented proof establishes a derived proposition with explicit
hypotheses, rather than the representation-theoretic premises used in that
source. The actual induced application in Ze80 Proposition 1.11 is separate.

The only direct imports are the exact published target and
`Filtration.MultiplicityAdditivityProof`. Their complete project import
closure consists of 26 modules under `Category`, `Filtration`, `Smooth` and
`Smooth.Transfer`. They provide invariant subspaces, actual smooth
subquotients, composition series, length, refinement, Jordan–Hölder
comparison and multiplicity additivity. The used declarations are the strict
count, kernel and covering lemmas of `LengthTwoMatching` and the exact
sequence equivalences `MultiplicityAdditivityProof.two_step_equivs`.

There is no project import or mathematical input from induction, Jacquet,
mirabolic or derivative theory, segment theory, analytic or tempered
classification, square-integrability, special heads or socles, any
multisegment construction or exhaustion, segment product irreducibility,
adjacent socle commutation, or any segment Jacquet or exponent formula.
Thus the closure excludes every task and conclusion on the host's independence
list, including the segment-socle portion of
`8e5b4563-0365-41c7-b134-70f2a0b36292`. No derivative exception is needed.
Development inspection of the exact theorem reports the independent
universes `uK,uG,uV,uW` and only `propext`, `Classical.choice` and `Quot.sound`.
Compilation is development evidence; independent acceptance and publication
of this proof are separate checks.
