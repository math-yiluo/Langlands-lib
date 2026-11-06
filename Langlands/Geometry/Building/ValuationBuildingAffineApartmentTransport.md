# Transport of the actual affine-apartment splitting

This internal derived unit works with two supplied `ValuationBuildingData`
for the same actual group over the same nonarchimedean local field
`F : Type u`. It retains every comparison premise and the source witness.
It does not construct building data or prove the unconditional
`RootValuationBuildingConstructionStatement`.

`range_cocharacterMapReal_comp_iso` identifies the range of the actual
cocharacter map after postcomposition by a torus isomorphism. The proof
checks pure tensors and uses the existing linear equivalence
`cocharacterRealCongr`.

`ApartmentSplitting.transport` retains the supplied derived group, its
inclusion, the derived torus and its embedding in the derived group, and
the central torus. It postcomposes the embeddings of both tori in `B₁.S`
by a supplied isomorphism `σ : B₁.S ≅ B₂.S`.

The remaining results assume the actual embedding square
`B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i`.
`normalizerEquivOfTorusIso` identifies the normalizer subgroups by the
identity on actual rational points.
`normalizingAut_comp_torusIso` obtains compatibility of their chosen
normalizing automorphisms by transporting the actual normalizing point
and using uniqueness of its torus automorphism.

`normalizerAction_compatible_of_comparison` uses an equivariant equivalence
of the existing quotient buildings, a compatible affine equivalence of
their apartments, and injectivity of the target apartment map. Applying
that map and cancelling it proves compatibility of the normalizer actions
on the apartments. No root comparison is needed for this step.

`ApartmentSplitting.transport_satisfiesAffineApartmentAxiom` assumes that
normalizer-action compatibility and a source
`SatisfiesAffineApartmentAxiom` witness. It proves all fields of the target
predicate. The derived-group and maximal-split-torus assertions are
unchanged. Closedness of the derived-torus embedding is preserved by
postcomposition with the isomorphism. Both embedding identities and the
split-component assertion follow from the actual embedding square.
The complementary real cocharacter ranges transfer under the submodule
order isomorphism induced by `cocharacterRealCongr`. Compatibility of the
chosen normalizing automorphisms transfers preservation of the derived
torus. The affine apartment equivalence and action compatibility transfer
triviality of the center action. The existing `hasAffineConjugations`
theorem supplies the final field for the target data.

The reference to KP Axiom 4.1.4 is the label of the unchanged Library
predicate in `FullValidity.AffineApartment`. This is a derivation from
that predicate and existing actual torus and cocharacter transport,
without a new literature assertion. All actual data, the torus square,
the affine action comparison and the source axiom witness remain
premises at every universe `u`.
