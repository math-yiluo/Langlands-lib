# Geometric quotient input at a twisted-fixed point

`UnramifiedTwistedChamberQuotientStatement` is a derived, unproved prerequisite
for the Lang correction route to `UnramifiedTwistedGeneratorChamberStatement`.
Its hypotheses are exactly those of that statement and of
`UnramifiedTwistedChamberThroughFixedPointStatement`, at arbitrary universe `u`.

## Data and conclusion

Let `F` be the supplied nonarchimedean local field, `K = inertiaFixedField F`,
`Γ = Aut(K/F)`, and `G_K = baseChanged F K G`. The supplied maximal split torus,
apartment class `D`, centralizer `C`, V6 compatibility, and coefficient stability
`hD` determine the same building `B` and coefficient action `A.action σ` as the
host statement. The map `c : Γ → G(K)` satisfies the same crossed-homomorphism
identity and is trivial on the fixing subgroup of a finite subextension. The
point `y` is fixed by every twisted action `z ↦ c σ • A.action σ z`.

Set `κ = 𝓀[F]` and `Ω = IsLocalRing.ResidueField (fixedFieldIntegers F)`.
A finite enumeration of `κ` is chosen by `Fintype.ofFinite`.
The algebra structure is exactly `(residueToFixedField F).toAlgebra`.
`fixedFieldResidueIsAlgClosure F` supplies its algebraic closure structure.
Thus these are the actual residue field of `F` and residue field of `K`, with
no auxiliary choice of an algebraically closed field.

The conclusion chooses `φ ∈ Γ` whose integer powers meet every fixing-subgroup
coset of every finite subextension, in exactly the sense used by
`UnramifiedTwistedGeneratorChamberStatement`. For this same `φ` it supplies
`B.HasFiniteFieldChamberQuotient κ Ω θ τ y`, where

- `θ(g) = c φ * rationalConjugate F K G φ g * (c φ)⁻¹`;
- `τ(z) = c φ • A.action φ z`.

Expanding that predicate, the conclusion supplies a connected reductive
`κ`-group scheme `R`, a subgroup `P ≤ B.fixer y`, a surjective homomorphism from
`P` onto the actual `Ω`-points of `R`, and a map on `P` restricting `θ` whose
reduction is canonical Frobenius descent. It also supplies an initial chamber
with the exact translated generic-facet closure presentation through `y`,
setwise fixation of that chamber by the kernel, and a member `h ∈ P` whose
translate is its `τ`-image. Stability of the initial chamber is not required.
The statement does not identify the existential subgroup with a particular
parahoric or the group scheme with a specified model's special fibre.

## Source and provenance

This is a derived input interface, not a numbered assertion of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023). The intended construction uses
Axiom 4.1.22(4), (5), (7) and Remark 4.1.23 (printed pp. 163–164, PDF pp. 194–195):
surjectivity of reduction, incident-facet/parabolic correspondence, and the
reduction kernel's fixation of incident facets. The chamber application is
Proposition 9.10.1, proof of (4) ⇒ (1) (printed p. 381, PDF p. 412), with
Proposition 9.10.4 (printed p. 382, PDF p. 413). The twisted action is that of
the proof of Theorem 10.6.1 (printed p. 397, PDF p. 428). The authors' corrections
and additions of 1 November 2024 are used with the book.

For this interface one must descend the twisted reductive quotient to the finite
residue field and identify its induced action with canonical Frobenius descent.
One must also construct the initial chamber, prove its kernel and orbit
properties, and choose a compatible dense generator. These are substantive
geometric obligations. The source motivates this packaging; the cited chamber
existence assertion alone does not supply the displayed quotient witnesses.
The separate conditional reduction uses Lang's theorem on the resulting actual
finite-field group. Neither this module nor that reduction proves the present
existence statement, the supplied building data's existence, or the final host
target unconditionally.
