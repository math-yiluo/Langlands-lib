# Canonical scalar sections base change on Cartesian affine squares

This internal prerequisite works in every common universe `u`. Let `X` and `Y`
be affine schemes, let `R` and `S` be commutative rings, and let
`φ : R ⟶ S`, `f : X ⟶ Spec R`, `f′ : Y ⟶ Spec S` and `g : Y ⟶ X` satisfy
`w : g ≫ f = f′ ≫ Spec.map φ`. Assume this actual square is Cartesian,
expressed by `IsPullback g f′ f (Spec.map φ)`, and let `M` be a
quasi-coherent object of `X.Modules`.

`isIso_scalarSectionsBaseChangeMap_of_isPullback_affine` proves that the
published canonical map

`scalarSectionsBaseChangeMap φ f f′ g w M : S ⊗[R] Γ_f(M) ⟶ Γ_f′(g* M)`

is invertible. Here scalar extension means Mathlib's `ModuleCat.extendScalars`
for the underlying ring homomorphism `φ.hom`, and `Γ_f` is the published
`relativeGlobalSections f`. `affineCartesianScalarSectionsIso` packages
precisely this map by `asIso`; its forward map is the specified canonical map.
There is no flatness, finiteness, noetherian or reducedness hypothesis.

The proof first supplies the internal adapter
`isIso_scalarSectionsBaseChangeMap_of_isPushout`. For a categorical pushout
of commutative rings `R → S`, `R → A`, `S → B`, `A → B`, it installs the
corresponding algebra and scalar-tower structures and applies the published
`isIso_pushoutAffineScalarSectionsMap`. The published
`scalarSectionsBaseChangeMap_affineAlgebraSquare` identifies that result with
the actual scalar sections map. `isPushout_of_isPullback_spec` reflects a
Cartesian square of spectra through the fully faithful spectrum functor and
passes from the opposite category to rings.
`isIso_scalarSectionsBaseChangeMap_of_isPullback_spectra` then uses
`Spec.preimage` to cover arbitrary morphisms between specified spectra.

Two transport lemmas preserve the actual map through the published scalar
sections composition formula. Invertibility can be detected after an
isomorphism presenting the target scheme
(`isIso_scalarSectionsBaseChangeMap_of_precomp_iso`). The proof cancels the
invertible sections map for the isomorphism square, the pullback composition
comparison and the scalar extension composition comparison; extension by the
identity ring map reflects isomorphisms. An isomorphism presenting the source
also transports invertibility
(`isIso_scalarSectionsBaseChangeMap_comp_source_iso`), by composing the
invertible canonical sections map for that isomorphism square with the given
map and the same comparison isomorphisms. Neither transport lemma needs
quasi-coherence.

For the affine result the proof presents `X` and `Y` by their canonical
`isoSpec` isomorphisms. It transports the Cartesian square using
`IsPullback.of_iso′` and applies the result for specified spectra.
Quasi-coherence of the coefficient pulled back along `X.isoSpec.inv` follows
from the existing restriction instance and `restrictFunctorIsoPullback`.
The two transport lemmas return invertibility of the original canonical map.

The provenance is internal: the argument derives these adapters from the
published pushout affine sections construction and canonical sections
composition and isomorphism results, together with Mathlib's spectrum,
Cartesian-square and restriction APIs. It claims no new literature theorem.
This pair proves the affine sections prerequisite; it does not prove higher
cohomology base change or the relative rigidified cube statement.
