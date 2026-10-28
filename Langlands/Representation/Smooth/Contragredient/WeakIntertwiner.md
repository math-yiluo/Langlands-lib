# Intertwiners represented by weak forms

This module proves that a bilinear form with the contragredient translation law
is the pairing of an actual intertwiner, when the target representation is
admissible and compact open subgroups are cofinal. It is the device used to turn
weakly convergent coefficient integrals into intertwining maps.

## Statement

`Langlands.exists_intertwiningMap_of_weakForm_of_compact_cofinal` works for a
topological group `G` and complex vector spaces `X`, `Y`. Its hypotheses are:

- `hcof`: every open subgroup of `G` contains a compact open subgroup;
- `π : Representation ℂ G Y` is smooth;
- `τ : Representation ℂ G X` is admissible;
- `Λ : Y →ₗ[ℂ] SmoothDual τ →ₗ[ℂ] ℂ` is a bilinear form with
  `Λ (π h y) ℓ = Λ y (smoothContragredient τ h⁻¹ ℓ)` for all `h`, `y`, `ℓ`.

It concludes that there is `f : π.IntertwiningMap τ` with
`smoothDualPairing τ ℓ (f y) = Λ y ℓ` for all `y` and `ℓ`.

## Proof

For fixed `y`, the functional `Λ y` on the smooth dual is fixed by the
contragredient action of the compact open subgroup `K` fixing `y`: this is the
translation law with `π k y = y`. Hence `Λ y` is a smooth vector of the double
contragredient. Restricting the codomain gives a linear map
`Φ : Y → SmoothDual (smoothContragredient τ)`, and the translation law is exactly
the statement that `Φ` intertwines `π` with the double smooth contragredient.

The Library supplies the evaluation map `smoothBidual` from `τ` to its double
smooth contragredient, with injectivity
`smoothBidual_injective_of_compact_cofinal` and, for admissible `τ`, surjectivity
`smoothBidual_surjective_of_compact_cofinal`. The resulting intertwining
equivalence `e` is inverted, and `f := e.symm ∘ Φ`. The pairing identity then
follows from `e (e.symm (Φ y)) = Φ y` and `smoothBidual_apply`.

## Provenance and scope

This is an internal derived lemma built only on the Library's smooth
contragredient API (`Contragredient.AdmissibleDualityProof`,
`Contragredient.LawsProof`). The bidual isomorphism it inverts is the Library's
formalization of Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter II, Proposition II.3.1 (as documented in
`Contragredient/AdmissibleDualityProof.md`); it is used here, not reproved. No
analytic hypothesis or integral appears in this module.
