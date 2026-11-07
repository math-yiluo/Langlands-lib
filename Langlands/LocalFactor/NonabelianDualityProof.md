# Dual functional equations for actual virtual local constants

`Langlands.LocalFactor.NonabelianSystem.dualFunctionalEquation` proves exactly
`DualFunctionalEquationStatement.{uF,uV}`. Its type has no additional hypotheses.
It retains every prime, independent field and representation carrier universes,
supplied normalized local-constant system, actual common-closure intermediate
field, nontrivial unitary additive character, regular Haar measures and exact
virtual element quantified in that proposition. The spectral clause retains
every complex parameter.

The implementation applies
`dualFunctionalEquation_of_generation_of_localAnalysis` to
`commonClosureDegreeZeroGeneration` and `padicAbelianLocalAnalysis`. Thus the
two premises of the earlier conditional assembly are discharged by their
separate proofs. The target statement and its imported pairs are unchanged.
The following paragraphs describe the implemented dependency chain.

For scalar abelian expressions, full Tate local analysis supplies the dual-Haar
epsilon equation at spectral parameter zero. The Fourier-volume adapter derives
the required integer-ring volume product from exactly `FourierDualMeasures`.
The unramified-twist clause at shift one identifies the inverse character's
epsilon at one with the normalized-absolute-value twist of that character at
zero. The conductor identities and the proved zero-parameter comparison then
give the product identity for the two actual abelian epsilon expressions.

The character-line adapter descends each continuous character of the actual
Weil subgroup through topological abelianization and the supplied reciprocity
equivalence. Normalization identifies the norm twist of its full
contragredient with the normalized-absolute-value twist of its inverse field
character. Rank-one agreement in the existing `IsSystem` replaces the system
values by the scalar expressions. This proves fixed-Haar duality on every
actual continuous character line.

The additive duality defect has an integer-linear kernel in the actual
continuous exact Grothendieck group. The proved twisted-dual induction
comparison and trace-character identities transport its vanishing from
character differences over larger intermediate fields to their inductions.
Existing self-dual measure existence supplies the measures needed over those
larger fields. Actual common-closure degree-zero generation puts the whole
degree kernel in the defect kernel. For any virtual element, subtract its
integer degree times the trivial character line, apply degree-zero vanishing,
and add back the trivial-line multiple. Consequently the defect vanishes on
every exact virtual element, giving the fixed-Haar unit product equal to one.

The spectral reduction applies that equation to the actual spectral twist at
`s`. The proved exact-quotient identity identifies its norm-twisted
contragredient with the twist at `1-s` of the untwisted contragredient. This
gives the second unit product for the existing `conditionalDeligneValue`, with
the original unshifted spectral convention.

Both clauses use the supplied measures under the unchanged
`FourierDualMeasures` condition, including convergence of the successive
actual Bochner integrals and the reflection identity. No duality law,
generation assertion, analytic theorem or system-existence assertion is added
to `IsSystem`. The proof is an internal composition of the named scalar,
representation-theoretic and common-closure results, with the source conventions
already recorded in the paired target statement.
