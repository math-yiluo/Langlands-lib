# The affine action of an actual opposite factor pair

This internal adapter derives the linear reflection formula for an actual supplied
opposite factor pair from its integral coroot formula. It then derives the full
affine reflection formula from the fixed-hyperplane predicate `HasRootReflections`.
That predicate is an explicit hypothesis of the affine-action results in this
module. The module does not prove it or the existence of opposite factor pairs.

The field `F : Type u` has arbitrary universe and the published nonarchimedean
local-field instances. The ambient group scheme, maximal split torus, apartment,
normalizer action and root groups are those of the supplied
`B : ValuationBuildingData G`. The final containment result uses the actual cover
in `P : ParahoricBuildingData G`.

`reflectionCoroot` is the class of `1 ⊗ ν` in the reduced translation space, where
`ν` is the integral coroot of the supplied pair. Its root pairing is two.
The imported `RelativeRoot.IsOppositeFactorPair.coroot_spec` supplies the
integral reflection formula without an additional factorization-existence
assumption. The inverse character action is the same reflection because that
reflection is an involution. Evaluating all roots shows that the normalizer
action on the real cocharacter space agrees with the desired reflection modulo
the common root annihilator. This proves
`translationAction_reflectionElement`; it requires neither apartment axioms
nor `HasRootReflections`.

The root functional has nonzero derivative because it evaluates to two on this
vector. It therefore vanishes at some apartment point. AS 1 fixes this point,
and the geometric affine reflection fixes it too. Equality of the linear parts
and equality at this point prove equality of the affine automorphisms.
This is `normalizerAffineEquiv_reflectionElement_of_hasRootReflections`.

Under `B.SatisfiesApartmentAxioms`, the normalizer action preserves the
published affine-root set `Ψ`, by its containment in the extended affine Weyl
group. Pulling back an affine root by the computed reflection gives exactly
`f - f.linear v • ψ`. Thus the constructed vector satisfies
`AffineRootSystem.IsCoroot Ψ ψ v`, even when the supplied root point's functional
`ψ` is only in `Ψ′`. Uniqueness of coroots for the rank-zero-compatible affine
root system identifies this vector with any supplied `IsCoroot Ψ ψ` vector.
The corresponding normalizer-action equality therefore holds for that vector
as well. These are the three results ending in
`_of_hasRootReflections` following the affine-action formula.

`ParahoricBuildingData.reflectionElement_mem_simplyConnectedImage` assumes
only `P.SatisfiesApartmentAxioms`, membership of the nonidentity point in its
root group, and the supplied actual pair. The pair's character action sends
`a` to `-a`; invariance of the relative-root set proves that `-a` is a root.
`ParahoricBuildingData.rootGroup_le_simplyConnectedImage`, imported from
`ApartmentRootCover`, then places both opposite factors and the
original root point in the actual simply connected image. Subgroup closure
places their literal product `p.1 * g * p.2` in that image. This result uses
neither `HasRootReflections` nor a substitute cover.

The provenance is derived: the constructions are deductions from the imported
integral pair consequences, the definitions of the actual normalizer action,
the existing affine-root-system coroot uniqueness theorem and the actual
root-group cover lifts. No new claim from external literature is introduced.
The module is a helper for the apartment-only affine Iwahori–Tits task. It
does not establish existence of opposite pairs, the whole simply connected
normalizer's affine image, the Tits axioms or corrected saturation.
