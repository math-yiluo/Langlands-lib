# Étale removal of the split maximal torus hypothesis

This is an internal derived construction. It combines the published affine
étale existence of split maximal tori, normality of prime localizations of
étale algebras over a normal domain, the split residue-field isomorphism
criterion, reflection of isomorphisms along field extensions, and the DVR
generic/special fibre criterion. No external-source translation is asserted.

All rings, fields, schemes and torus indices are in an arbitrary universe `u`.
In the local section, `R` is a local integrally closed integral domain with a
specified fraction field `K`. The source `M` is reductive, the target `G` is
smooth and affine over `Spec R`, and the underlying map of `f : M ⟶ G` is an
open immersion. Its actual base change to `K` is assumed to be an isomorphism.
An open immersion already supplies monicity. No split torus is an input.

`isIso_field_of_injective` applies over an integral domain with a fraction
field, independently of the local and geometric hypotheses above. For an
injective ring map `R → L` to a field, it extends that map to `K → L` by
`IsFractionRing.lift`. The equality of the corresponding spectrum maps and
the direct/iterated pullback comparison transfer the given generic
isomorphism to the actual base change of `f` along `Spec L → Spec R`.

`isIso_residue_of_local_extension` applies to any local homomorphism of local
rings `R → B`. The induced map between their canonical residue fields gives
a scalar tower `R → κ(R) → κ(B)`. The direct/iterated pullback comparison
identifies `f` over `κ(B)` with the scalar extension of `f` over `κ(R)`.
Faithfully flat reflection along the field extension therefore proves that
invertibility over `κ(B)` implies invertibility over `κ(R)`. The map being
reflected is the given `f`, not a chosen isomorphism between its objects.

For `closedResidueField_isIso`, choose an affine étale chart `Spec A → Spec R`
with a point `x` above the closed point and a closed fibrewise maximal
coordinate split torus in the pulled-back source. The induced algebra
structure makes `A` étale over `R`. Set `p = x.asIdeal` and
`B = Localization.AtPrime p`. Integrally closedness of `R` and étaleness
give that `B` is an integral domain. The equation specifying `x` implies
`p.under R = maximalIdeal R`; the maximal ideal of `B` contracts to `p`, so
`R → B` is local. Flatness of the étale algebra and the localization makes
this local extension faithfully flat.

Consequently `R → B` is injective, and so is `R → Frac B`. The first helper
gives the generic isomorphism for the source and target pulled back to
`Spec B`. The chosen torus also pulls back to a closed fibrewise maximal
coordinate split torus there. Reductivity of the source, smoothness and
affineness of the target, and openness of `f` all persist under these base
changes. The split local-domain residue-field criterion from
`SplitDvrOpenIsomorphism` applies to this data over `B`; no DVR hypothesis on
`B` is required. The spectrum-map scalar-tower identities identify its
conclusion with invertibility of the original `f` over `κ(B)`.
`isIso_residue_of_local_extension` then proves invertibility over `κ(R)`.

The DVR section replaces the local normal-domain hypotheses by the
`IsDiscreteValuationRing R` instance, retaining the given fraction field,
reductive source, smooth affine target, open immersion, and generic
isomorphism. `isIso_of_dvr` supplies the derived residue-field isomorphism
and the given generic isomorphism to
`Langlands.AlgebraicGeometry.isIso_of_generic_special`. Smoothness of `M`
and `G` provides its structure-map hypotheses. The resulting isomorphism
of underlying schemes reflects to an isomorphism of group schemes.

`dvrIso : M ≅ G` is `asIso f` using that result. The simplification lemma
`dvrIso_hom` states that its forward homomorphism is exactly `f`.
The total-base conclusion here is restricted to a DVR. The local section
proves a residue-field conclusion over a local normal domain. Applying
these results to an actual generic closure and proving the unrestricted
monomorphism closed-immersion statement remain separate work.
