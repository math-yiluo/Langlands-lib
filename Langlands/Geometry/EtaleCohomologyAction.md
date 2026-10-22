# Group actions on étale cohomology through automorphisms of the scheme

Author: Worker 13. Combines `Langlands.Geometry.EtaleAutomorphism` and
`Langlands.Cohomology.TranslationAction` (this submission) with Worker 13's
published `Langlands.Geometry.EtaleDerivedSections`.

Let `Y : Scheme.{u}`, let `R : Type u` be a commutative ring, and let `G` be a
group in any universe. Let `ρ : G →* (Aut Y)ᵐᵒᵖ` be a homomorphism into the
opposite of Mathlib's automorphism group. Translation is contravariant in the
automorphism, so this convention gives a left action on cohomology.

## Translation data

- `aut ρ g` is the automorphism of `g`. `aut_mul` gives
  `aut ρ (g * h) = aut ρ g ≪≫ aut ρ h`, and `aut_one` gives
  `aut ρ 1 = Iso.refl Y`. Both follow from Mathlib's `Aut_mul_def`.
- `translateBy R ρ g` is `EtaleAutomorphism.translate` of `aut ρ g` on étale
  module sheaves.
- `sectionsTop R` is sections over the terminal object of `Y.Etale`; an
  instance proves it additive.
- `compIso` is `translateComp` followed by `translateCongr` for `aut_mul`.
  `oneIso` is `translateCongr` for `aut_one` followed by `translateId`.
- `sections_compIso` and `sections_oneIso` derive the coherence conditions
  from `sectionsIso_comp`, `sectionsIso_congr` and `sectionsIso_id`.
- `data R ρ` assembles these into `TranslationAction.Data` for
  `sectionsTop R`. Its `sections g` is `EtaleAutomorphism.sectionsIso` of
  `aut ρ g`.

## Equivariant sheaves and cohomology

- `EquivariantSheaf R ρ` is `TranslationAction.Equivariant (data R ρ)`. Its
  objects are étale module sheaves `F` with maps from the translates by every
  `g`, satisfying the cocycle conditions.
- `cohomologyRep R ρ F n : Rep R G` is Mathlib's `Rep.ActionToRep` applied to
  `TranslationAction.cohomologyAction` for Mathlib's chosen injective
  resolution of `F`.
- `cohomologyIso R ρ F n` identifies the underlying module with the published
  étale cohomology `EtaleDerivedSections.cohomology Y R n` of `F`. It uses the
  published `EtaleDerivedSections.sectionsIso` and `cohomologyIso`.

## Provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), Theorem 5.7, printed p.313, considers the
action of `Gal(F̄/F)` on étale cohomology `H^{n-1}(S_K(N), W)` of Shimura
varieties with coefficients. Worker 13 read this passage in the original.
Such an action arises when the Galois group acts by automorphisms on a base
change to an algebraic closure, and the coefficient sheaf carries a
compatible equivariant structure. This module constructs the resulting
representation for any group acting on any scheme and any equivariant étale
module sheaf. It is derived infrastructure.

Not treated here: the Galois group action on a base change, the canonical
equivariant structure of constant or pulled-back sheaves, continuity of the
action, compactly supported cohomology, Hecke operators, and the Shimura
varieties themselves.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules other than `EtaleAutomorphism` and `TranslationAction`
are present in Library commit `2839e6bae86085a8a220122cf5eb434176a57d4c`.
