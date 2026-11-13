# Field transport of supercuspidal twists and `GL₁` classes

Helper module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeOperationStatement`
(Henniart (2000), §§3.7–3.8, page 451). It shows that the supercuspidal-side
pullback `completionSupercuspidalLatticeEquiv v h K f` used by
`henniartCompositeMap` carries character twists to character twists and `GL₁`
classes to `GL₁` classes. These are the supercuspidal halves of the twist and
character clauses of `Correspondence.LatticeMap.OperationProperties`. The Weil
halves are in `HenniartCompositeOperationWeil.lean`.

These are routine transport facts with no direct counterpart in the literature.
Throughout, `χE ∘ f = χF` is stated pointwise as

`∀ (a : F.Carrierˣ) (b : E.Carrierˣ), (b : E.Carrier) = f (a : F.Carrier) → χE b = χF a`.

## General p-adic fields (`Langlands.VirtualRepresentation.PadicSupercuspidal`)

Let `f : F ≃ₐ[ℚ_p] E` be an isomorphism of p-adic fields. Let `χE` and `χF` be
field characters (`Correspondence.QuasiCharacter`) of `E` and `F` with
`χE ∘ f = χF`.

- `unitaryLatticeEquiv_unitaryCharacterTwistLatticeEquiv F E f χE hχE χF hχF hrel x`:
  `unitaryLatticeEquiv F E f` takes `unitaryCharacterTwistLatticeEquiv E χE hχE x` to
  `unitaryCharacterTwistLatticeEquiv F χF hχF (unitaryLatticeEquiv F E f x)`. Here
  `hχE` and `hχF` say the characters have modulus one. The proof applies
  `Supercuspidal.fieldUnitaryLatticeEquiv_unitaryTwistLatticeEquiv` (from
  `Langlands/VirtualRepresentation/Supercuspidal/FieldTransportOperations.lean`)
  with `σ = f`, `χE ∘ det` and `χF ∘ det`. The required identity
  `χF (det g) = χE (det (σ g))` follows from `hrel` and
  `GeneralLinear.determinant_fieldEquiv`, which says `det (σ g) = σ (det g)`.
- `rankOneSupercuspidalObjectFieldPullbackIso F E f χE χF hrel`: an isomorphism from
  the pullback along `f` of the `GL₁` representative
  `rankOneSupercuspidalObject E χE` to `rankOneSupercuspidalObject F χF`. Both are
  the character line `ULift ℂ`, and the underlying map is the identity. Under the
  pullback, `g` acts by `χE (det (σ g))`, which equals `χF (det g)` by the
  identity in the previous item.
- `includeUnitary_unitaryLatticeEquiv_rankOne F E f χE χF hrel y hy`: suppose `y`
  includes as the generator of the rank-one class
  `⟨1, rankOneSupercuspidalClass E χE⟩` (this is `hy`). Then
  `unitaryLatticeEquiv F E f y` includes as the generator of
  `⟨1, rankOneSupercuspidalClass F χF⟩`. The proof uses
  `includeUnitary_unitaryLatticeEquiv` and `Supercuspidal.fieldLatticeEquiv_generator`,
  then the previous isomorphism to identify the classes.

## Completion form (`Langlands.Global`)

Let `v` be a finite place of `F` and `h : residuePrime v = p`. Let
`f : K ≃ₐ[ℚ_p] F_v` be an isomorphism onto the prime-transported package
`padicFieldAt v h`. Let `χ` and `χ'` be field characters of `K` and of
`padicField v` with `χ' ∘ f = χ`, written pointwise as above (this is `hrel`).
Theorem `exists_completionQuasiCharacter` in `HenniartCompositeOperationWeil.lean`
gives such a `χ'` for any modulus-one `χ`.

- `completionSupercuspidalLatticeEquiv_unitaryCharacterTwistLatticeEquiv v h K f χ hχ χ' hχ' hrel y`:
  `completionSupercuspidalLatticeEquiv v h K f` takes
  `PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv (padicField v) χ' hχ' y` to
  `PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K χ hχ` applied to the
  pullback of `y`.
- `includeUnitary_completionSupercuspidalLatticeEquiv_rankOne v h K f χ χ' hrel y hy`:
  suppose `y` includes as the generator of
  `⟨1, rankOneSupercuspidalClass (padicField v) χ'⟩`. Then its pullback includes as
  the generator of `⟨1, rankOneSupercuspidalClass K χ⟩`.

Both proofs substitute `h`. After that, `padicFieldAt v rfl` is definitionally
`padicField v` and `padicFieldAtSupercuspidalLatticeEquiv v rfl` is the identity.
The general lemmas then apply with `E = padicFieldAt v rfl`. The lattice carrier
universe `uV` is arbitrary; the composite map uses `uV = uF`.

All declarations depend only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
