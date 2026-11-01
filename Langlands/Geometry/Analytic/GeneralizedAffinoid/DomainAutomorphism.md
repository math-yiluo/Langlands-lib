# Bounded stabilizer actions on full represented domains

Authors: Worker 56 and Worker 36.

This module constructs bounded section automorphisms of each supplied full
represented affinoid domain from the automorphisms of the base that preserve
its locus. The section maps, their inverses and the action laws are outputs
of the construction.

The coefficient field `K : Type u` is complete, normed and ultrametric. The
base `A` and every representing algebra are actual closed quotients of finite
positive-polyradius Tate algebras. The valuation may be trivial, the quotient
may have nilpotents or be zero, and the represented locus may be empty.
The input `U : Domain K A` supplies the published full representation
property against all presented positive-polyradius affinoids in this
universe. No extra section map or automorphism is input.

`locusStabilizer U` is the subgroup of `Aut A` preserving `U.locus`
setwise under the existing spectrum action
`g • x = BanachSpectrum.comap g.inv.toBoundedRingHom x`.
`mem_locusStabilizer` exposes its image equality, and `smul_mem_locus`
deduces point membership from that equality. Individual points and the
chosen quotient presentation need not be fixed.

`hasImageIn_comp_baseMap` proves that composing any bounded map out of
`U.algebra` with `U.baseMap` has spectrum image in `U.locus`. Pulling a
target seminorm back along that bounded map produces an eligible point
of `U.algebra`. Consequently `boundedHom_ext` proves equality of two
bounded maps out of `U.algebra` whenever their composites with the base
map agree, even if that common composite is a twisted base map. It uses
the full representation property's uniqueness clause and never assumes
faithfulness of spectrum points.

For `g : locusStabilizer U`, `twistedBase_hasImageIn` proves image
containment for `U.baseMap.comp g.hom`. Its spectrum comap is the inverse
stabilizer acting on the original structural comap. The inverse
stabilizer therefore preserves its image. Testing the representation
property on the actual algebra `U.algebra` constructs
`stabilizerSectionMap U g`, with the proved equation

```text
stabilizerSectionMap U g ∘ U.baseMap = U.baseMap ∘ g.hom.
```

`stabilizerSectionMap_one` and `stabilizerSectionMap_mul` compare full
bounded maps using `boundedHom_ext` and this equation. Multiplication
acts by composition with the right factor applied first. Applying these
laws to `g` and `g⁻¹` proves both inverse identities, constructing
`stabilizerSectionAut U g : Aut U.algebra`.
`stabilizerSectionAction` packages the constructed automorphisms as a
monoid homomorphism. `stabilizerSectionAction_baseMap` gives the
elementwise structural equation.

For an actual restriction `f : U ⟶ V` and one base automorphism
preserving both loci, `stabilizerSectionMap_restriction` proves that
restriction commutes with the two section operators. Both sides are
bounded maps from `V.algebra` to `U.algebra`; their composites with
`V.baseMap` agree by the restriction's stored base equation. The full
representation property of `V` then identifies them.

`stabilizerSectionAction_spectrumMap` proves equivariance of
`U.spectrumMap` for the actual inverse-comap section and base actions.
Evaluation of the section base equation for `g⁻¹` on each seminorm proves
the equality. It does not require injectivity of the structural spectrum
map.

This is internal derived content from the published full representation
property, the actual bounded-map category and the existing spectrum
action. The group-law and inverse packaging follows the existing
strict rational stabilizer-action construction by Worker 36 in
`Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerAction`.
The new section maps instead use the full all-positive-radius unique
factorization directly, and the new restriction theorem applies to
arbitrary supplied full domain representations.

The module imposes no topology on `Aut A` or its stabilizer and asserts
no continuity in the group parameter. Analytic automorphism topology,
comparison with all compact analytic domains, structure sheaves,
general analytic spaces and their sites remain separate work.
