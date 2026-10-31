# Canonical scalar extension of affine global sections

This internal prerequisite uses the actual affine module-sheaf pullback functor and
global-section functors. Fix an arbitrary universe `u`, commutative rings
`R S : CommRingCat.{u}`, a ring map `φ : R ⟶ S`, and `p = Spec.map φ`.
For every module sheaf `M` on `Spec R`, `affineSectionsPullbackMap φ M` is the
`R`-linear map `Γ_R(M) → Res_φ Γ_S(p^*M)` obtained by applying global sections
to the pullback unit `M → p_*p^*M`, followed by the published `pushforwardΓIso`.

`affineScalarSectionsMap φ M` is its adjunct under extension/restriction of
scalars. Its source is `S ⊗_R Γ_R(M)` in Mathlib's left-factor scalar-extension
convention, and its target is `Γ_S(p^*M)`. The Hom-equivalence and unit formulas
identify this as the canonical pullback-induced map; the tensor-generator formula
sends `1 ⊗ m` to the semilinear pullback image of `m`. The map is natural in
arbitrary coefficient morphisms `M → N`.

For `M = tilde V`, `affineScalarSectionsMap_tilde` identifies this map with the
published `tildePullbackIso φ V` after the standard tilde global-section
identifications. The equality is proved on generators using
`tildePullbackIso_adjoint_toOpen_top`; extension-of-scalars extensionality proves
the full equality. Every other map in the equality is an isomorphism, so the
canonical scalar section map is an isomorphism on associated sheaves.
For a quasi-coherent `M`, the tilde–global-sections counit `M.fromTildeΓ` is an
isomorphism by pinned Mathlib. Naturality along this counit transfers the result
to `M`. `affineScalarSectionsIso` packages this result, with exactly the canonical
map as its forward morphism.

No flatness, finite generation, finite presentation, noetherian, reducedness or
nonzero-ring hypothesis is assumed. The isomorphism result requires precisely
quasi-coherence of `M`; the map and its compatibility identities do not. This file
concerns ordinary sections on spectra and proves no positive-degree cohomology
base change, Čech comparison, or relative cube theorem.

The construction and proofs are internal consequences of the published
`Langlands.AlgebraicGeometry.Modules.TildePullback` and pinned Mathlib
`AlgebraicGeometry/Modules/Tilde.lean` and
`Algebra/Category/ModuleCat/ChangeOfRings.lean` at commit
`5ed2965256430c3649e86755f9576b54eca72435`. No new external mathematical assertion
is used. The local transparency option supports elaboration through the existing
scheme-module wrappers and adds no mathematical premise.
