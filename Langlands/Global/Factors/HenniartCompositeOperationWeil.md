# Restriction of Weil lattices along a group isomorphism and the operations

Helper module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeOperationStatement`
(Henniart (2000), §§3.7–3.8, page 451). It shows that the Weil-side pullback
`completionWeilLatticeEquiv v h K f` used by `henniartCompositeMap` commutes with
the contragredient, the character twist and the rank-one character classes. These
are the Weil halves of the contragredient, twist and character clauses of
`Correspondence.LatticeMap.OperationProperties`.

The results are routine transport facts with no direct counterpart in the
literature. Restricting a representation along a group isomorphism uses the same
vector space, so each comparison below is the identity map on carriers.

## Finite-dimensional representations (`Langlands.FiniteRepresentation`)

- `restrictDualEquiv φ A : Equiv (restrict φ (dual A)) (dual (restrict φ A))`, for
  a monoid homomorphism `φ : G →* H` of groups and a complex representation `A` of
  `H`. The underlying map is the identity of `Module.Dual ℂ A`. It intertwines
  because `(φ g)⁻¹ = φ g⁻¹`.
- `restrictTwistEquiv φ χ A : Equiv (restrict φ (twist χ A)) (twist (χ.comp φ) (restrict φ A))`.
  The underlying map is the identity, and it intertwines by definition.

The rank-one comparison uses the existing Library equivalence
`FiniteRepresentation.restrictCharacterLineEquiv` from
`Langlands/Global/Factors/RelativeWeilLocalEpsilon.lean`.

## Unitary lattices along `e : G ≃ₜ* H` (`Langlands.VirtualRepresentation.Weil`)

- `restrictBasisEquiv_twistBasisEquiv e χ b`: restricting the twist of a basis class
  `b` by `χ : H →ₜ* ℂˣ` gives the twist of the restricted class by
  `χ.comp e`. The proof uses `restrictTwistEquiv` on a representative.
- `restrictBasisEquiv_characterClass e χ`: restricting the rank-one class
  `⟨1, continuousIrreducibleCharacterClass χ⟩` gives
  `⟨1, continuousIrreducibleCharacterClass (χ.comp e)⟩`. The proof uses
  `restrictCharacterLineEquiv`.
- `restrictUnitaryLatticeEquiv_unitaryTwistLatticeEquiv e χ hχ hχe x`: on the
  unitary lattices, `restrictUnitaryLatticeEquiv e` takes
  `unitaryTwistLatticeEquiv χ hχ x` to
  `unitaryTwistLatticeEquiv (χ.comp e) hχe (restrictUnitaryLatticeEquiv e x)`. Here
  `hχ` and `hχe` say that `χ` and `χ.comp e` have modulus one. The proof applies
  `Finsupp` induction and uses the basis lemma on single elements.
- `unitaryTwistLatticeEquiv_congr hχ h₁ h₂`: equal characters give equal unitary
  twists, whatever the modulus-one proofs.
- `restrictBasisEquiv_dualBasisEquiv e b` and
  `restrictUnitaryLatticeEquiv_unitaryDualLatticeEquiv e x`: restriction commutes with
  the contragredient on basis classes and on unitary lattices. These need
  `[IsTopologicalGroup G] [IsTopologicalGroup H]`. The proofs use
  `restrictDualEquiv` and then `Finsupp` induction.

## Completion form (`Langlands.Global`)

Let `v` be a finite place of `F` and `h : residuePrime v = p`. Let
`f : K ≃ₐ[ℚ_p] F_v` be an isomorphism onto the prime-transported package
`padicFieldAt v h`, and let `φ = completionWeilEquiv v h K f : W_K ≃ₜ* W_{F_v}`.

- `exists_completionQuasiCharacter v h K f χ hχ`: every modulus-one field character
  `χ` of `K` has the form `χ' ∘ f` for some modulus-one field character `χ'` of
  `padicField v`. Formally: `∀ a b, (b : F_v) = f a → χ' b = χ a`. The proof
  substitutes `h` and takes `χ'` to be the published inverse pullback
  `PadicField.ConductorTransport.quasicharacter K (padicFieldAt v rfl) f χ`.
- `weilCharacter_comp_completionWeilEquiv v h K f e e' he χ χ' hχ`: suppose
  `rec_{F_v}(φ w) = f (rec_K w)` for all `w`, with `rec` given by `reciprocityUnits`
  for the candidates `e'` and `e` (this is `he`), and suppose `χ' ∘ f = χ` (this is
  `hχ`). Then `(weilCharacter (padicField v) e' χ').comp φ = weilCharacter K e χ`.
  Theorem `exists_geometric_completionReciprocity` in
  `CompletionReciprocityTransport.lean` supplies `he` for a geometric `e'`.
- `completionWeilLatticeEquiv_unitaryDualLatticeEquiv v h K f y`:
  `completionWeilLatticeEquiv` commutes with `LocalWeil.unitaryDualLatticeEquiv`.
- `completionWeilLatticeEquiv_unitaryFieldCharacterTwistLatticeEquiv v h K f e e' χ hχ χ' hχ' hcomp y`:
  suppose `hcomp : (weilCharacter (padicField v) e' χ').comp φ = weilCharacter K e χ`.
  Then `completionWeilLatticeEquiv` takes the twist
  `LocalWeil.unitaryFieldCharacterTwistLatticeEquiv (padicField v) e' χ' hχ'` to
  `LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e χ hχ`.
- `includeUnitary_completionWeilLatticeEquiv_rankOne v h K f e e' χ χ' hcomp y hy`:
  assume `hcomp` as above. Suppose also that `y` includes as the generator of the
  rank-one class `rankOneWeilCharacterClass (padicField v) e' χ'` (this is `hy`). Then
  `completionWeilLatticeEquiv v h K f y` includes as the generator of
  `rankOneWeilCharacterClass K e χ`. The proof uses
  `includeUnitary_restrictUnitaryLatticeEquiv`,
  `restrictLatticeEquiv_generator` and `restrictBasisEquiv_characterClass`.

All declarations depend only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

The finite-representation restriction/dual equivalence is shared with the relative-Weil development through `Langlands.Weil.Representation.RestrictionDual`.
