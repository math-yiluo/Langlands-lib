# Actual Artinian and dual-number pointed Picard fibres

This internal construction compares the actual augmented-Artinian Picard
deformation groupoid with the previously computed pointed dual-number
groupoid. It uses `Deformation.ArtinianDualNumbers`,
`Picard.ArtinianTestDeformations`, and `Picard.DualNumberPointedTangent`,
ordinary fibre-product identities, and ordinary bundle pullback. It invokes
no external deformation or algebraicity theorem.

Fix a commutative ring `k : Type u`, a field `K : Type u` with its specified
`k`-algebra structure, and an actual morphism `f : X → Spec k`.
`residueSpace f` is the chosen actual fibre product `Spec K ×_k X`;
`residueStructure f` is its projection to `Spec K`.
`artinianSpace f` is the actual relative space over the augmented test
`ArtinianTest.dualNumbers k K`. These are the relative spaces used by
the original Picard pseudofunctor, rather than newly assumed models.

`spaceIso f` is the explicit pullback-associativity isomorphism from
the dual-number thickening of `residueSpace f` to `artinianSpace f`.
Its two arrows are constructed by the pullback universal property,
and the inverse identities follow by the two projection tests.
`spaceIso_hom_fst` and `spaceIso_hom_snd` give its actual projections.
`closedPoint_spaceIso` identifies its composite with the zero section
with the original Artinian reduction map. `scale_spaceIso` proves that
it intertwines the actual geometric maps induced by `ε ↦ c ε`, for
every `c : K`, including zero.

Ordinary bundle pullback along this isomorphism gives
`bundleEquivalence`. Its unit and counit use the existing pullback
composition and identity comparisons. `reductionComparison` combines
the proved zero-section square with those same comparisons.
For an actual bundle `M` on the residue fibre, `pointedFunctor` applies
`StructuredArrow.map₂` with that comparison and the identity on `M`.
Thus it retains the chosen reduction identification, with its ordinary
pullback coherence. The equivalence criterion for `map₂` proves
`pointedFunctor_isEquivalence`, and `pointedEquivalence` packages the
resulting equivalence. The two displayed object and arrow formulas
identify its operations with ordinary pullback of the actual bundle and
bundle isomorphism.

`Classes f M` is the quotient of the actual Artinian dual-number
deformation groupoid by isomorphism. A private categorical construction
descends an equivalence to these quotients, using the unit and counit
for the inverse identities. Applied here it gives `classEquiv`.
`classEquiv_mk` identifies the map on representatives.
`classEquiv_ordinary_val` records the ordinary class of the pulled-back
bundle, using the proved canonical tensor-preservation theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`.

`restrictClass c` is induced by the original Artinian restriction functor
along `ArtinianTest.dualScale k K c`. To prove
`classEquiv_restrictClass`, the proof uses injectivity of the published
pointed-to-ordinary-class comparison, then quotient induction. On an
actual bundle representative, functoriality of ordinary pullback and
`scale_spaceIso` identify the two resulting bundle classes. Hence the
scalar operation on `Classes f M` is actual Artinian test restriction.

`classesAddCommGroup` transfers the published normalized tensor addition
through `classEquiv`, and `classAddEquiv` records additivity. If the
residue structure morphism is separated and quasi-compact,
`classesModule` reflects the known module laws along this injective
additive equivalence, using the proved scalar compatibility.
`classLinearEquiv` packages the linear equivalence. For each ordered
affine cover of the actual residue fibre, `classH1LinearEquiv` composes
it with `pointedTangentH1LinearEquiv`, obtaining an equivalence with the
actual derived relative structure-sheaf `H¹`.

If `f` is proper, `residueStructure_isProper` obtains properness of the
residue fibre by base change. This supplies the separatedness and
quasi-compactness needed above. `finiteDimensional_classes` transfers
the published finite dimensionality of pointed dual-number classes
along the inverse linear equivalence.

All constructions retain arbitrary universe `u` and arbitrary, possibly
imperfect fields `K`. The groupoid comparison itself needs neither
properness nor separatedness. No coefficient-field structure is imposed
on general Artinian tests. The construction handles this specific
dual-number test and every actual residue-fibre bundle; it does not
construct a hull or prove formal versality, effectivity, algebraization,
openness of versality, or existence of a smooth scheme atlas.
