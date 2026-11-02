# Affine pushforward base change

This internal prerequisite proves invertibility of the actual ordinary-module
`pushforwardBaseChange` in a cartesian square when the original vertical
morphism is affine and the coefficient sheaf is quasi-coherent. The base
morphism and the schemes are arbitrary in universe `u`.

On an affine square over spectra, the proof combines the published canonical
scalar sections comparison with quasi-coherence of affine pushforward and the
published scalar-to-sheaf comparison. The general proof uses the affine open
factorization and stalk detection from `DirectImageAffineCriterion`, with its
local pasting argument adapted to the affine-morphism hypothesis. No finite
projective or constant-rank condition is used. Open-base comparison and the
composition identity identify the local isomorphisms with the specified
adjunction-defined map. The definition `affinePushforwardBaseChangeIso` bundles
that same map as an isomorphism.

All declarations lie in
`Langlands.AlgebraicGeometry.Modules.DerivedSections`.
`isIso_pushforwardBaseChange_of_isPullback_affine` treats affine total spaces
over spectra. The general lemma
`isIso_pushforwardBaseChange_of_isAffineHom` assumes precisely
`IsAffineHom f`, `M.IsQuasicoherent`, and `h : IsPullback p f' f b`.
It imposes no flatness, finite-presentation, or surjectivity hypothesis on `b`
and no noetherian, quasi-compact, or affineness hypothesis on the base schemes.
Its conclusion concerns the canonical map from `b* f_* M` to `f'_* p* M`.
`affinePushforwardBaseChangeIso_hom` identifies the bundled forward map with
that canonical comparison by reflexivity.

The provenance is internal: the unit combines the Library's
`AffineCartesianSectionsBaseChange`, `AffineDirectImageBaseChange`,
`CoherentClosure`, and `PullbackQuasicoherent` results. The general local
reduction adapts the already published proof of
`AffineSectionsData.isIso_pullback_baseChange` from
`DirectImageAffineCriterion`, supplying its affine comparison directly from
affineness rather than from finite projective constant-rank sections.

This is a prerequisite for a comparison of geometric descent data with
coalgebras. It does not construct that comparison or prove stack algebraicity.
