# Unramified-twist independence of stable images

Author: Worker 4803. Module `Langlands.Correspondence.HenniartTwistIndependenceProof`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers), `uV` (supercuspidal carriers), `uE` (local-constant values in
the candidate properties), all independent.

## Results

- `stableImage_unramifiedTwist`. Fix a p-adic field `K` and a geometric
  reciprocity candidate `e` of `K` (`IsGeometricReciprocity K e`). Assume
  `CandidateExistenceStatement.{uK, uW, uV, uE, uK}`. Let `σ` be an irreducible
  Weil class of `K`, and let `z₁, z₂ : ℂˣ`. Suppose the unitary classes `σ₁`, `σ₂`
  satisfy `σ₁ = weilUnramifiedTwist K z₁⁻¹ σ` and `σ₂ = weilUnramifiedTwist K z₂⁻¹ σ`,
  and have stable images `y₁`, `y₂`. Then
  `unramifiedTwistLatticeEquiv K z₁ y₁ = unramifiedTwistLatticeEquiv K z₂ y₂`,
  with `y₁`, `y₂` included into the full supercuspidal lattice. This is the
  body of `UnramifiedTwistIndependenceStatement` at one field.
- `unramifiedTwistIndependence_of_reciprocity`. This theorem gives
  `CandidateExistenceStatement.{uK, uW, uV, uE, uK} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE}`.
  The second hypothesis is used only to obtain a geometric reciprocity
  candidate of each field.

Both hypotheses are published Library propositions. Neither result asserts them.

## Provenance

Internal proof of the published `UnramifiedTwistIndependenceStatement` (module
`HenniartStableMapStatement`). That statement is Henniart (2000), §4.4, printed
p. 453 (PDF p. 15). §4.4 refers to Henniart (1993), §4.3, printed p. 349
(PDF p. 11), for the extension `π_σ := π_{σ|·|^s} ⊗ |·|^{-s} ∘ det`. There,
Henniart shows the extension is independent of `s`: for a second choice `s'`,
the character `|·|^{s-s'}` has finite order, and the finite-image map commutes
with twisting by finite-order characters.

The Lean proof uses the same idea in the Library's setting, but weakens finite
order to modulus one. The twist clause of a candidate
(`LatticeMap.TwistCompatibility`, Henniart 2000, 3.8 (a)) covers every field
character of modulus one, so the proof only needs `‖z₁ z₂⁻¹‖ = 1`.

## Proof

Write `w = z₁ z₂⁻¹`.

1. Composition of Weil twists (`Weil.twistBasisEquiv_mul`,
   `localUnramifiedCharacter_mul`) shows that `σ₂` is the twist of `σ₁` by the
   unramified Weil character with value `w`.
2. Under the geometric candidate `e`, that character is the pullback of the
   unramified field character `fieldUnramified K w` (`weilCharacter_fieldUnramified`).
   Write `a = rec(g)`, which is possible because the reciprocity map is surjective
   (`reciprocityHom_surjective'`). Both `σ₁` and its twist `σ₂` are unitary, so
   `Weil.norm_eq_one_of_isUnitaryClass_twist` gives
   `‖fieldUnramified K w a‖ = 1` for every unit `a`. At the uniformizer this value
   is `w`, so `‖w‖ = 1`.
3. `exists_common_candidate₂` (module `HenniartExtensionBijective`) uses candidate
   existence at the product of the two finite quotients. It gives one candidate
   `Φ` with `Φ σ₁ = y₁` and `Φ σ₂ = y₂`. `IsStableImage.exists_generator` writes
   `y₁` as the generator of a unitary supercuspidal class `π₁`.
4. `candidate_twist_generator`, the twist clause of `Φ` for `fieldUnramified K w`,
   sends the twist of `σ₁` to the twist of `π₁` by `fieldUnramified K w ∘ det`.
   By `unitaryFieldCharacterTwist_fieldUnramified_val` and step 1, the twist of
   `σ₁` is `σ₂`. Since `Φ` is a function, `y₂` is the generator of the twist of
   `π₁`, which is the unramified twist of `π₁` by `w`.
5. Then `z₂ y₂ = z₂ w π₁ = z₁ π₁ = z₁ y₁`
   (`PadicSupercuspidal.unramifiedTwistBasisEquiv_mul`).

For `unramifiedTwistIndependence_of_reciprocity`, a normalized family `eC` from
`CommonClosureReciprocityExistence` (at the canonical topological data) gives the
geometric candidate `baseReciprocityCandidate K eC`
(`baseGeometricReciprocityProof`). The proof then applies
`stableImage_unramifiedTwist`.

Standard axioms only.
