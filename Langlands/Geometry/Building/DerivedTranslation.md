# Reduced translation spaces through an actual derived inclusion

Authors: Worker 27 and Worker 1631. The bundled `DerivedRootTransport`
support is Worker 1631's work.

For a field `k : Type u`, retain the supplied actual derived inclusion and
split-torus square of `Rational.DerivedRelativeRoots`: `D` is affine and
locally of finite type, `G` is affine and smooth, `d : D ⟶ G` represents the
actual derived subgroup, and

`j ≫ d = CommGroupScheme.groupHom e ≫ i`

for `j : T.toGrp ⟶ D`, `i : S.toGrp ⟶ G` and `e : T ⟶ S`. The tori `T`,
`S` and `A` are split. A map `c : A ⟶ S` supplies a central composite with
`i`, and the product of `e` and `c` is flat and surjective on schemes.
No isogeny or surjectivity assumption is made on `e` itself.

The definition `derivedTranslationEquiv` constructs

`TranslationSpace j ≃ₗ[ℝ] TranslationSpace i`,

where both spaces are the original real cocharacter spaces modulo the common
kernels of their actual relative roots. On representatives its forward map
is exactly `cocharacterMapReal e`; `derivedTranslationEquiv_mk` proves the
formula by reflexivity.

The proof first establishes
`exists_eq_cocharacterMapReal_add_of_centralComplement`. This helper needs
only the split tori and their flat-surjective product. The actual product
torus is viewed as a commutative group scheme. Its product morphism is an
epimorphism on schemes and is therefore surjective on real cocharacters,
by `cocharacterMapReal_surjective_of_epi`. Projecting a preimage to its two
factors expresses every `v : V S` as

`v = cocharacterMapReal e w + cocharacterMapReal c z`.

On pure tensors this identity is the original product homomorphism on
cocharacters; additivity extends it to the real tensor product.

Next, `cocharacterMapReal_mem_rootAnnihilator_derived_iff` proves that
`cocharacterMapReal e` preserves and reflects the common root kernel.
The natural pairing identity `eval_cocharacterMapReal` and the actual
derived-root bijection prove both implications.

The definition `derivedTranslationMap` descends the original linear map to
the two quotients. Its representative formula is `derivedTranslationMap_mk`.
The root-kernel equivalence proves injectivity in
`derivedTranslationMap_injective`. For surjectivity, use the displayed
two-factor decomposition of an ambient real cocharacter. Every ambient
root vanishes on the central factor, so the second term lies in the root
annihilator and disappears in the quotient. This proves
`derivedTranslationMap_surjective`. The equivalence is constructed from
these two properties.

Finally, `rootForm_derivedTranslationEquiv` identifies each original ambient
root form with its corresponding derived root form. Quotient induction
reduces this assertion to the natural evaluation identity on the original
real cocharacters.

This is an internal construction from the existing perfect pairing and
split-torus surjection results, the actual root bijection, and central-root
vanishing. It does not construct the supplied tori or product, a source
apartment, its full omega compatibility, or the final normalizer-image
theorem.

The integrated module also exposes
`cocharacterRange_sup_eq_top_of_centralComplement`, expressing the product
spanning result as a supremum of linear ranges;
`comap_rootAnnihilator_derived`, expressing the same root-kernel comparison
as a submodule equality; and
`centralComplement_cocharacterRange_le_rootAnnihilator`, isolating the
central factor's vanishing. These are the additional reviewed interfaces
used by the normalizer-action comparison. The existing decomposition,
quotient maps and representative formulas are retained.
