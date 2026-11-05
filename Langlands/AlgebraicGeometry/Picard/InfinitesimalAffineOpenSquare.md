# Sections of the actual square on arbitrary affine opens

This internal prerequisite constructs the induced morphisms of a commuting
scheme square on inverse images of an open, and proves the actual global-sections
ring pullback on every affine open of the relative square used by the Picard
comparison.

For a commuting square with maps `i₁ : Y₀ ⟶ Y₁`, `i₂ : Y₀ ⟶ Y₂`,
`j₁ : Y₁ ⟶ Y`, `j₂ : Y₂ ⟶ Y` and equation `w : i₁ ≫ j₁ = i₂ ≫ j₂`,
the common source open is `((i₁ ≫ j₁) ⁻¹ᵁ U)`. The definitions
`leftRestriction` and `rightRestriction` are the ordinary induced scheme
morphisms from this open to `j₁ ⁻¹ᵁ U` and `j₂ ⁻¹ᵁ U`. The second uses `w`
to identify the inverse-image opens. Their inclusion formulas retain the
original maps `i₁` and `i₂`, and `restriction_comm` gives their compatibility
with the restrictions `j₁ ∣_ U` and `j₂ ∣_ U`.

The main local conclusion, `appTop_isPullback`, takes an arbitrary field `k`,
commutative `k`-algebras `R,A,B,C`, and a categorical pullback of the actual
underlying ring maps `p : R →ₐ[k] A`, `q : R →ₐ[k] B`, `a : A →ₐ[k] C`,
`b : B →ₐ[k] C`. It uses the exact relative schemes
`(relativeSpace f).obj (affineBase k _)` and their actual `affineBaseMap`
morphisms for an arbitrary scheme morphism `f : X ⟶ Spec k`. For every affine
open `U` of the relative scheme over `R`, it proves

```text
IsPullback (j₁ ∣_ U).appTop (j₂ ∣_ U).appTop
  (leftRestriction i₁ j₁ U).appTop
  (rightRestriction i₁ i₂ j₁ j₂ w U).appTop.
```

The result requires no properness or finiteness condition on `f`, and no
surjectivity or nilpotence condition on the square. It therefore applies in
particular to the host infinitesimal-gluing problem. The quantifier over all
affine opens permits affine refinements inside arbitrary overlaps.

The proof is implemented in three steps. First,
`isPullback_of_flat_pushouts` installs algebra structures from the supplied
actual ring maps, obtains the fourth algebra compatibility from the original
square equation, and applies
`InfinitesimalAffineSquareSections.isPullback_of_pushouts`. Three given pushout
identifications and the identity pushout produce the new square. Flatness is
an explicit hypothesis on the base map.

Second, `affineCube_appTop_isPullback` obtains these three pushouts from actual
cartesian scheme faces by Mathlib's `isPushout_appTop_of_isPullback`. Flatness
of the total projection gives flatness of its actual global-sections map.
The two vertical compatibility equations and the top square equation give
the remaining actual ring-map equations by contravariance of `appTop`.
`restricted_appTop_isPullback` pastes the ordinary open-restriction pullbacks
with the three cartesian faces to apply this argument over any affine open.
Affineness of the base schemes and flatness of the total projection are
retained explicitly in this generic version.

Finally, the actual relative-space projection is flat because it is the base
change of `f`, and every morphism to the spectrum of a field is flat.
`relativeProjection_isPullback` supplies all the cartesian faces, with the
composite face obtained by pasting. The canonical `Scheme.ΓSpecIso` and its
inverse naturality formulas transport the original ring pullback to the
global sections of the spectra. Thus the conclusion concerns actual `appTop`
maps on the chosen scheme opens, with no unproved coordinate identification.

The provenance is internal, derived from the published relative-space,
infinitesimal flat-base-change and tensor-coordinate interfaces and Mathlib's
affine pullback, restriction, flatness and spectrum-section constructions.
This module proves a local ring property. Global effectivity and full
faithfulness for the Picard comparison remain separate obligations.
