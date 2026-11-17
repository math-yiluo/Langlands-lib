# Affine generation of actual subgroup identity jets

Let `G` be an affine group scheme over `Spec R`, let `b : S ⟶ Spec R`,
and let `h : H ⟶ G_S` be an actual group-scheme homomorphism whose
underlying scheme map is a closed immersion. The base scheme `S` is
arbitrary.

`IdentityJet.ambient_coordinateMap_span` says that for each affine open
`U` of `S`, the functions obtained from `AffineCoordinates.algebra G`
via the actual map `ambientProjection G b h` span
`Γ(H.total, H.structure ⁻¹ U)` over `Γ(S,U)`. The scalar action is the
one induced by the actual structure morphism of `H`.

Assume also that `H` is affine over `S`, as required by the existing
affine identity-jet section comparison. Write `B` for the chosen ambient
coordinate algebra, `I` for its counit kernel, and
`B_n = B / I^(n+1)`.
`IdentityJet.ambientQuotientCoordinates_restrict_span` says that the
restrictions of the existing global sections
`ambientQuotientCoordinates G b h n : B_n → Γ(module H n, ⊤)`
span `Γ(module H n,U)` over `Γ(S,U)` for every affine base open `U`.
These are functions on the actual closed identity neighborhood, pushed
forward along its actual projection to `S`. The theorem holds at every
order `n`, with no smoothness, finiteness, or noetherian assumption.

The intermediate theorem `quotientCoordinates_restrict_span` works
for any relatively affine group scheme `K/T`, any actual morphism
`j : K.total ⟶ Spec B`, and any ideal `I` satisfying the existing
predicate `VanishesAtIdentity K j I`. If the corresponding coordinates
span the group functions on an affine base open, their quotient classes
give spanning sections on the actual identity jet over that open.

The private base-change lemma proves the first spanning claim using
`LineHom.sectionsTensorHom_bijective`. Affine base change functions
are tensor products of ambient global functions and base functions.
Surjectivity of sections along the given closed immersion lifts an
arbitrary subgroup function to such a tensor. Tensor induction then
expresses its restriction in the required span. The coordinate
group-scheme isomorphism and the global-sections/Spec isomorphism
transport all ambient functions to the fixed algebra `B`.

For the quotient step, the proof uses the surjective linear map from
the affine group section ring to its augmentation-power quotient,
followed by `IdentityJet.sectionsEquiv.symm`. Applying this map to the
known span gives the entire actual jet section module.
`sectionsEquiv_restrict_quotientCoordinates` identifies the images
with the restrictions of the specified global quotient-coordinate
sections. Finally `ambientProjection_vanishesAtIdentity` discharges
identity vanishing in the ambient case.

This is an internal consequence of the imported affine base-change,
closed-immersion, coordinate, and actual identity-jet APIs. It is a
generation result supporting the actual parabolic Grassmannian
comparison; the classified-quotient kernel comparison and determinant
ampleness remain separate obligations.

`ambientProjection_over` identifies the actual structure map of the ambient
coordinate projection. `ambient_coordinateMap_algebraMap` consequently
identifies ambient scalar functions with the scalars pulled back along
`b` and the actual structure morphism of `H`. These formulas prove that
restriction of the prescribed global quotient coordinates is `R`-linear.
The definition `ambientQuotientCoordinateLinear` packages that map on
each affine base open. Its target uses restriction of the actual
`Γ(S,U)` module action along the algebra map induced by `b`.

The definition `ambientTensorCoordinates` extends this map to
`Γ(S,U) ⊗[R] B_n →ₗ[Γ(S,U)] Γ(module H n,U)`. The formula
`ambientTensorCoordinates_tmul` sends `a ⊗ z` to `a` times the
restriction of the existing global section `ambientQuotientCoordinates z`.
`ambientTensorCoordinates_surjective` proves its surjectivity under the
given closed-immersion hypothesis: the range of an extended linear map
is precisely the base-linear span of the original image, which is the
previously proved span. No condition on smoothness or finiteness is
added by this construction.
