# Relative module cohomology and actual abelian-sheaf pushforward

This internal construction works with actual schemes in arbitrary universe
`u` and actual sheaves of modules, without flatness, properness, or
quasi-coherence assumptions. Let `f : X ⟶ Spec R`.

`relativeGlobalSectionsForgetIso f` identifies the actual relative global
sections followed by forgetting `R` scalars with the actual absolute global
sections followed by forgetting `Γ(X, ⊤)` scalars. Its components are the
identity on the underlying groups of sections.
`forgetRelativeDerivedSectionsIso f n` applies the canonical exact-target
comparison `exactPostcompIso` to this isomorphism. It identifies underlying
relative module cohomology with the right-derived functor of underlying
absolute global sections. The degree is any `n : ℕ`.

`relativeCohomologyIso f M n` then composes with the existing canonical
`compComparison` for forgetting actual module scalars on the scheme. It is
an isomorphism from the underlying group of actual relative cohomology of
`M` to right-derived abelian global sections of the actual underlying
abelian sheaf. Invertibility is supplied by the existing acyclicity of the
underlying abelian sheaf of an injective scheme module.

The normalization results retain the published actual comparisons:

- `forgetRelativeDerivedSectionsIso_app` computes the new exact-target
  comparison on the same chosen injective resolution using
  `DerivedPlus.rightDerivedCompIsoOfResolution`.
- `forgetRelativeDerivedSectionsIso_restrictScalars` proves that first
  applying the existing `relativeCohomologyRestrictScalarsIso` and then the
  new relative forgetting comparison gives exactly the existing absolute
  `forgetDerivedSectionsIso`.
- `relativeCohomologyIso_restrictScalars` proves the corresponding identity
  with the published absolute `cohomologyIso`. These are equalities of
  actual morphisms, with the scalar-restriction maps retained.
- `relativeCohomologyIso_hom_naturality` proves compatibility with every
  actual coefficient-module morphism.
- `relativeCohomologyIso_baseRing` proves compatibility with the existing
  `relativeCohomologyBaseRingIso` for every map `φ : R ⟶ S` and structure
  maps `f` and `f'` satisfying `f = f' ≫ Spec.map φ` on the same scheme.

For the scalar-restriction normalization, the proof uses the existing
coherence theorem `rightDerivedCompIsoOfResolution_hom_comp` with the
identity-component comparison between absolute forgetting and restriction
of scalars followed by relative forgetting. The induced isomorphism on
sections equals `relativeGlobalSectionsForgetIso`. The explicit
normalization on the chosen injective resolution then cancels the forward
and inverse scalar-restriction comparisons. The coefficient result uses
naturality of the exact-target comparison and `compComparison`. The
base-ring result unfolds the existing base-ring isomorphism into its two
scalar-restriction comparisons and applies the normalization on both sides.

Now let `h : X ⟶ Y` and `g : Y ⟶ Spec R`.
`forgetRelativeDerivedSectionsIso_pushforward` assumes vanishing positive
higher direct images of `M` along `h`. It proves compatibility of the
canonical relative `pushforwardComparison h g` with exact forgetting of
its target scalars and the specified actual underlying sections comparison.
The proof applies `compComparison_postcomp`; compatibility on actual
sections is reflexivity.

For `relativeCohomologyIso_pushforward`, assume `IsClosedImmersion h` and
`IsIso h.base`. This theorem identifies the actual relative module
pushforward comparison with the canonical abelian-sheaf comparison through
`relativeCohomologyIso`. Its final morphism retains the derived image of
`pushforwardForgetIso h`. The source uses `h ≫ g`. The abelian-sheaf
comparison uses the actual pushforward along `h.base` and
`abelianPushforwardSectionsIso h`. Closed-immersion higher-direct-image
vanishing supplies the previous lemma's premise. The proof composes that
lemma with `twoStepComparison_pushforward`.

The provenance is internal: identity comparisons on actual sections,
exact-target derived comparisons, their published coherence, and the
actual two-factor pushforward comparison. The result supplies the relative
scalar and degreewise pushforward comparison needed for Picard obstruction
naturality. Identification with the Ext-defined
`UnitSheafPushforward.cohomologyPushforwardEquiv`, the resulting actual
obstruction comparison, and the exact field Picard-stack atlas remain
further obligations.
