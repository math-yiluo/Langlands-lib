# Supercuspidal uniqueness from local converse

This internal assembly discharges the system-uniqueness premises of
`SupercuspidalUniquenessReduction` using the published theorems
`LocalClassField.commonClosureReciprocityUniqueness` and
`LocalFactor.NonabelianSystem.unique`. It retains independent field,
Weil-parameter-carrier and automorphic-carrier universes.

`arithmeticPairEpsilonComparison_of_systems` proves the original
`ArithmeticPairEpsilonComparison` for any two supplied local-constant
assignments certified as systems. Their reciprocity families may be supplied
separately. The proof applies the existing comparison reduction: each
system's normalization and the published reciprocity uniqueness theorem
identify the families, and the published same-family system uniqueness
theorem identifies the assignments. Thus the complete arithmetic
epsilon-certificate predicates agree for every nontrivial additive
character, actual pair of parameter classes, coefficient and exponent.
The existing predicate retains its existence and universal clauses over
admissible continuous data, geometric Frobenius and the complex argument.
No family or system is constructed.

`supercuspidalCorrespondenceUniqueness_of_localConverse` supplies the same
proved system uniqueness to the existing correspondence uniqueness
reduction. That reduction compares the independently supplied families,
base candidates and arithmetic systems of two actual correspondences,
identifies their rank-one maps, and uses local converse in a strong
induction on rank. It obtains test surjectivity and self-dual measure
existence from the supplied correspondence predicates. Those steps remain
implemented in the imported reduction.

The Prop-valued
`SupercuspidalCorrespondenceUniquenessFromConverseStatement` expresses this
conditional result over every prime and every p-adic field, retaining the
original all-field local-converse statement at automorphic carrier
universes `uA,uA` as its sole premise. The following theorem proves that
proposition. No generation or system-uniqueness premise remains.

The final two theorems combine this conditional uniqueness with a supplied
proof of the original correspondence-existence proposition, first for one
field and then over all fields. They choose the supplied correspondence
witness and use uniqueness to identify every other witness with it. The
all-field theorem concludes the unchanged
`SupercuspidalCorrespondenceStatement`, with both its local-converse and
all-field existence inputs still displayed.

The provenance is entirely internal composition of published declarations.
This module proves neither local converse nor correspondence existence,
and it supplies no reciprocity family, local-constant system or
correspondence. It therefore does not prove the closed all-field
supercuspidal correspondence without hypotheses. The existing dedicated
local-converse and existence work remains necessary.
