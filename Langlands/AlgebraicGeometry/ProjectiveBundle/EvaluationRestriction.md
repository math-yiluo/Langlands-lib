# Restriction of actual local evaluation morphisms

This is derived infrastructure for gluing the local projective evaluation maps.
It uses the actual sections and line bundles of `EvaluationMorphism`, the
adjunction section maps in `Modules/PullbackAffineSections` and
`Modules/SectionPullbackBridge`, and the proved invariance and naturality
of the maps in `LinearSystem/BundleComparison` and
`LinearSystem/RelativeMorphism`. It introduces no external mathematical
assertion or new representability premise.

For a module sheaf `N` on `X` and opens `A ≤ B`, `openPullbackIso` is the
canonical isomorphism from the pullback of `N` first to `B` and then to `A`
to the direct pullback to `A`. It is the composition of `pullbackComp` with
`pullbackCongr` for the equality of the two open-inclusion morphisms.
The lemma `openPullbackIso_hom_openSection` proves that this isomorphism
carries the pullback of the actual converted section over `B` to the
converted restriction of that section over `A`.

The implemented proof first identifies `openSection` with
`sectionPullbackLE` for the inclusion of the open subscheme. It cancels
the inverse restriction-to-pullback comparison, uses its presheaf
naturality and the formula for the adjunction unit under this comparison,
and combines the remaining restriction maps. The global-section pullback
bridge and the composition, equality-transport and restriction laws for
`sectionPullbackLE` then prove the two-step section comparison.

Fix a scheme morphism `p : X → S`, a module sheaf `M` on `S`, a line bundle
`L` on `X`, and an actual module-sheaf morphism `ev : M → p_* L`.
For a frame `e` on `U` and opens `T ≤ W ≤ U`,
`localEvaluationSections_restrict` applies the two-step comparison to the
evaluated basis sections. Naturality of `ev` and restriction of the actual
basis identify the resulting section with the one constructed directly
over `T`.

If these concrete sections generate pointwise over the inverse image of
`W`, `localEvaluationSections_restrict_generate` proves that the sections
constructed over `T` generate as well. The proof pulls back the generating
family and transports it through `openPullbackIso`; the section comparison
identifies it with the actual smaller-open family. Thus generation over
`T` is a consequence, rather than a second hypothesis.

The morphism equation `evaluationBase_restrict` is the actual commutative
square of the two inverse-image-open morphisms and the open inclusions.
With the generation hypothesis above, `localEvaluationMap_restrict`
proves the equality of scheme morphisms

`localMap(T) ≫ P(T → W) = (p⁻¹T → p⁻¹W) ≫ localMap(W)`.

Here `P(T → W)` is `RelativeProjectiveSpace.map` for the actual base-open
inclusion. The proof transports the pulled-back sections by
`openPullbackIso`, invokes invariance of the relative linear-system map
under this line-bundle isomorphism, and applies its pullback naturality
with the proved base square.

All schemes have arbitrary common universe `u`; no affine, noetherian or
abelian-scheme hypothesis is added. The finite frame has size `n + 1`.
This unit proves restriction compatibility under the stated pointwise
generation hypothesis. It does not prove that hypothesis for abelian
schemes, construct a glued global map, establish an embedding, or prove
the host large-level representability statement.
