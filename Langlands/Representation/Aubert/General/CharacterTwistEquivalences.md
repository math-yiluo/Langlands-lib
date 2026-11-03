# Scalar twists of general normalized parabolic functors

This internal construction compares the existing general normalized induction
and Jacquet functors with a scalar character twist. The ambient group is any
locally compact nonarchimedean group, and its universe and the representation
carrier universe are independent. The character has open kernel and is assumed
trivial on the specified radical. No reductive structure, admissibility,
finite length, compact parabolic quotient, continuous Levi projection or
unimodularity assumption is needed for these comparisons.

For an actual semidirect decomposition `P = M ⋉ U`, the projection property
places `m(p)⁻¹ p` in `U`. Applying the character proves
`χ(p) = χ(m(p))`. Scalar multiplication commutes with the positive
half-modulus in the existing inducing action. The published
`Induction.smoothInductionTwistEquiv`, followed by transport through this
equality, therefore gives `normalizedInductionCharacterTwistEquiv`.
It sends a function `f` to `x ↦ χ(x) f(x)`; its inverse multiplies by
`χ(x)⁻¹`. The evaluation laws record both formulas.
Postcomposition by a linear intertwiner commutes with character
multiplication, giving `normalizedInductionCharacterTwistIso` on the full
smooth categories. The published invariance of irreducibility under scalar
twists and isomorphisms proves the corresponding induction irreducibility
equivalence.

For Jacquet restriction, the existing localized quotient at the trivial
character is identified with the ordinary coinvariant quotient by
`Jacquet.Localization.trivialEquiv`. The published
`Jacquet.twistActionTwistEquiv` identifies the ordinary quotients, including
the common inverse-half normalization. Transport back to localization gives
`normalizedJacquetCharacterTwistEquiv` on the actual functor carriers.
Both directions send the class of a vector to the class of that same vector.
Surjectivity of the localized quotient map then proves naturality on the full
smooth category. The carrier equivalence preserves the property of being a
zero object. Applying this to each proper standard radical inside a closed
Levi proves `isCorollaryLeviCuspidal_characterTwist_iff`.

These are derived constructions from the cited published Lean definitions and
proofs, without an external literature attribution. The proofs use actual
smooth induced functions, coinvariant quotients, subgroup inclusions and the
given semidirect decomposition. The general comparison extends the existing
GL block-Levi calculation in
`Langlands.Representation.Parabolic.CharacterTwistEquivalences` to
`Langlands.Aubert.General`; no GL identification is assumed.

Triviality of a chosen character on the radicals remains an explicit input.
This module supplies no central unitarizer, positive invariant form, geometric
filtration, Jacquet exponent bound or rational-point self-association theorem.
In particular, it does not prove
`RationalPointFamily.RationalRankOneSelfAssociationStatement`.
