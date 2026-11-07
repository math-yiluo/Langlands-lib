# Affine models for spans of affine schemes

This internal construction starts with actual affine schemes `X`, `Y`, and `Z` and actual maps `i : Z ⟶ X` and `j : Z ⟶ Y`. Its model is the spectrum of the pullback of the two maps on global sections. The cocone maps compose the canonical `isoSpec` maps with the spectra of the two ring projections.

If `i` is a closed immersion, its global-section map is surjective. The canonical locally ringed pushout theorem from `AffineSchemePushoutProof` then transports along the three `isoSpec` isomorphisms to give a pushout for the original affine span in locally ringed spaces. Naturality of `isoSpec` identifies the displayed maps exactly.

If `j` is integral, its global-section map is integral, as follows by isomorphism invariance and the affine spectrum criterion. `IntegralSchemePushoutAffineProperties` gives integrality of the first spectrum map and the closed-immersion property of the second, which are preserved by composition with the `isoSpec` isomorphisms. These are intermediate affine models for the global pushout construction; no global existence theorem is claimed here.
