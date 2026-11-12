# Retractions in quotients from comaximal central kernels

Worker 148. This internal algebraic construction combines the published
`SimpleBlockQuotient` and `ComaximalRestriction` helpers for the retraction step
in Renard VII.4.2 (i), printed p.243 / PDF p.249. It does not establish the
geometric or adjunction inputs of the classification theorem.

Let `rho`, `tau` and `chi` be complex representations of a group `G`, and let
`S` be a subrepresentation of `rho` equipped with an equivariant isomorphism
`e : S -> tau`. Suppose `tau` is irreducible. Let `a : B -> G` be a monoid
homomorphism with central image, and suppose the kernels of the `C[B]` actions
on `tau` and `rho/S` sum to the whole group algebra. Given a surjective
intertwiner `q : rho -> chi`, every nonzero intertwiner `j : tau -> chi`
has an equivariant retraction `r : chi -> tau`, with `r j = id`.

The group, central monoid and three representation carriers have independent
universes. The result assumes no topology, admissibility, finite length or
finite-dimensionality. The supplied `j` is injective by irreducibility; its
existence is an input.

The proof writes `1 = x + y`, with `x` killing `tau` and `y` killing `rho/S`.
Thus `y` acts as the identity on `tau`, and its action on `rho` lands in `S`.
Centrality makes these actions equivariant. Restricting the action on `rho`
to `S` and composing with `e` gives `p : rho -> tau`; the inverse of `e`
followed by inclusion gives `s : tau -> rho`. The action `E` of `y` on `chi`
satisfies `E q = q s p` by naturality and `E j = j`. The published
`simpleBlockQuotient_retraction` then supplies the claimed left inverse.

`quotientRetractionOfComaximal` chooses this retraction, and
`quotientRetractionOfComaximal_comp` proves its left-inverse identity.
This is derived internal content: it assembles the central-action
construction with the simple-block quotient theorem. It does not assert
that any particular Jacquet module has the required subrepresentation or
comaximality, or that second adjointness supplies the nonzero map `j`.
Those applications, Frobenius reciprocity and the remaining Langlands
classification arguments are separate obligations.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
version dated 9 July 2026, VII.4.2 (i), printed p.243 / PDF p.249; registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
