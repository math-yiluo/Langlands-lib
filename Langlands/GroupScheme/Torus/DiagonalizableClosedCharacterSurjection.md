# Local character surjections for closed diagonalizable inclusions

This internal construction identifies the character maps on the previously
constructed local restriction cover of a closed diagonalizable subgroup
inclusion as surjections. It is derived from the Library's affine
closed-immersion coordinate criterion, explicit diagonalizable group maps,
and base-change comparison isomorphisms.

The imported theorem `baseChangeIso_restrictMap` from
`DiagonalizableAutomorphismLocality` supplies compatibility of the canonical
diagonalizable base-change isomorphisms with character restriction on every
scheme test. This module reuses that published theorem.

Over a nonzero coefficient ring, `surjective_of_isClosedSubgroup_restrictMap`
shows that a closed subgroup map given by character restriction has a
surjective full character map. The coordinate map of a closed immersion
of affine schemes is surjective. A monomial outside the image of the
character map has zero coefficient in every element of the image of the
group-algebra map, whereas its own coefficient is one. Nonzeroness of
the coefficient ring rules this out.

`surjective_of_closed_baseChange` extends this criterion to any nonempty
scheme mapping to the original affine base. Take a residue field at one
point, use pullback-composition coherence to identify the direct change of
base, and use the canonical diagonalizable comparison to obtain the same
restriction map over that field.

For a closed inclusion `f : D_R(Γ) ⟶ D_R(Λ)` with finitely generated
`Λ`, `restrictionCharacterMap_surjective` applies this criterion on each
member of `restrictionCover f`. Each chosen neighborhood contains its
indexing point, so it is nonempty; the local map equals the base change
of the original closed inclusion. The definition `restrictionSurjection`
retains the chosen character map and its proof of surjectivity.

Torsion is retained in both character groups, and the original ring may
have zero divisors or nilpotents. No connectedness assumption is imposed.
