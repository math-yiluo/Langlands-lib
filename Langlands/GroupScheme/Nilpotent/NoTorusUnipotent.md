# Nilpotent groups without tori and central torus quotients

For every field `k : Type u`, let `G` be a smooth connected affine group scheme
over `Spec k`. `NilpotentNoTorusUnipotentStatement.{u}` asserts that `G` is
unipotent if it is geometrically nilpotent and every homomorphism from a
`k`-torus to `G` has trivial all-test range.
`nilpotentNoTorusUnipotent` proves this proposition.
Here geometric nilpotence is precisely `IsNilpotentGroupScheme G`,
nilpotence of the point group over the chosen algebraic closure.
There is no assumption on the cardinality, perfectness or characteristic
of the field.

The proof `IsNilpotentGroupScheme.isUnipotent_of_no_torus` passes to
`K = AlgebraicClosure k`. Smoothness and affineness are preserved by pullback,
and the published geometric-connectedness theorem supplies connectedness.
The published nilpotent base-change theorem makes `G_K` nilpotent and
therefore solvable. The published geometric cocharacter-vanishing theorem
uses centrality of torus homomorphisms and descent in the full commutative
centre to show that every `Gm_K → G_K` is zero. This step uses no smoothness
assumption on the centre.

Apply the algebraically closed solvable no-cocharacter criterion from
`Absolute.CharacterCocharacter` to conclude that `G_K` is unipotent.
The published field-reflection theorem for unipotence of affine group
schemes descends this conclusion to `G`.

The final theorem `nilpotentCentralTorus` proves the exact published
proposition `NilpotentCentralTorusStatement.{u}`. The existing construction
`IsNilpotentGroupScheme.centralTorusQuotient` supplies an actual central
maximal torus `T` over the original field and a smooth connected affine
quotient `Q`, together with its projection `q : G → Q`. It already proves
that `Q` is geometrically nilpotent and that every torus homomorphism into
`Q` has trivial all-test range. The preceding theorem makes `Q` unipotent.
All the other data and the original fppf quotient certificate are retained
from that construction.

Thus the conclusion includes an actual central maximal torus inclusion
`i`, affineness and unipotence of `Q`, and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.
The quotient certificate means that the projection is flat, surjective
and locally of finite presentation and that its kernel equals the stated
all-test range. It does not impose pointwise surjectivity on every test.

These proofs are internal deductions from the imported nilpotent,
commutative descent, character and quotient results. They do not use the
general `NoTorusUnipotentStatement` as a theorem or any maximal-torus
base-change preservation result deduced from it. The nonnilpotent case of
the parent no-torus theorem remains open.
