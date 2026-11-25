# Local and archimedean effect of a Hecke determinant twist on cuspidal pairs

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaAutomorphicTwist`). It supplies three groups of
facts about the published twist `heckeDeterminantTwist` by an arbitrary Hecke character
`χ` (Library `Langlands/Automorphic/HeckeTwist/*`), used to build the automorphic Hecke Euler
family in the proof of `AssociatedGammaStatement` (Henniart 2000, Théorème 2.3: the global
functional equation is applied to the twisted pair `(Π ⊗ χ, Π')`). The results are internal
deductions from the Library definitions; there is no separate literature theorem.

## (A) Local classes of a twisted presentation

For a cuspidal spectral presentation `P` of `S` and a Hecke character `χ`:

- `heckeDeterminantTwist_localComponent_isIrreducible_iff`,
  `heckeDeterminantTwist_localComponent_isAdmissible_iff`: the local component of
  `P.heckeDeterminantTwist χ` at `v` is irreducible (admissible) iff that of `P` is. Proof:
  the published equivalence `heckeDeterminantTwistLocalComponentEquiv` with the multiplied
  local component, then the published local statements
  `LocalRealization.heckeDeterminantTwist_isIrreducible_iff` / `_isAdmissible_iff`.
- `heckeDeterminantTwist_hasIrreducibleAdmissibleComponents`: the same at every place.
- `determinantQuasiCharacter_quasicharacterBase`: `χ_v ∘ det` on `GL_(r+1)(F_v)`, with `χ_v`
  transported to the canonical `p`-adic package by `quasicharacterBase`, is the local
  determinant character `χ.finiteLocalDeterminant (r+1) v`
  (`finiteLocalDeterminant_eq_finiteComponent_det`).
- `isCharacterTwist_heckeDeterminantTwist_padicClass` (**A**): the canonical `p`-adic class of
  the twisted component is `IsCharacterTwist` of the class of `P`'s component by
  `quasicharacterBase v (χ.finiteComponent v)`. The witnesses are the two `padicObject`s; the
  equivalence is `heckeDeterminantTwistRepresentationEquiv` followed by the inverse of
  `heckeDeterminantTwistLocalComponentEquiv`, after rewriting the twisting character by the
  previous lemma.

## (B) Archimedean parameters under a twist trivial at infinity

Assume `χ.HasPrescribedInfinityComponent 1` (`χ` is trivial on the archimedean ideles).

- `HeckeCharacter.infiniteDeterminantCharacter_eq_one`: `χ(det a) = 1` for archimedean `a`
  (via `AdelicGL.determinant_ofInfinite`).
- `ArchimedeanGL.characterDifferential_eq_zero_of_eq_one`: the derivative at the identity of
  a trivial smooth character is `0` (its coordinate extension is the constant `1`).
- `heckeEnvelopingShift_eq_id`: the enveloping shift `U ↦ U + dχ(U)` is the identity
  (zero differential on generators, then `UniversalEnvelopingAlgebra.hom_ext`).
- Consequently the twist equivalence commutes with the compact action
  (`heckeDeterminantTwistEquiv_compact_of_trivial`) and with the enveloping action
  (`heckeDeterminantTwistEquiv_enveloping_of_trivial`), hence with the place compact and Lie
  actions at real and complex places.
- `HasRealPlaceParameter.heckeDeterminantTwist`,
  `HasComplexPlaceParameter.heckeDeterminantTwist` (**B**): every archimedean standard-module
  parameter of `S` is one of `S.heckeDeterminantTwist χ`; the embedding is composed with the
  twist equivalence, as in the published `HasRealPlaceParameter.of_equiv`.

## (C) Contragredients of twisted pairs

- `heckeDeterminantTwist_heckeDeterminantTwist_inv`: `(S ⊗ χ) ⊗ χ⁻¹ = S` as operator
  realizations (the two multipliers compose to the identity, by
  `evaluate_heckeDeterminantMultiplier` and `adelicDeterminant_inv`).
- `IsContragredientOf.heckeDeterminantTwist_inv` (**C**): if `Sd` is a contragredient of `S`,
  then `Sd ⊗ χ⁻¹` is a contragredient of `S ⊗ χ`, by the published
  `IsContragredientOf.of_heckeDeterminantTwist` applied with `χ⁻¹` to `S ⊗ χ`.
