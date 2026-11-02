# The trace of a finite flat morphism on sections of a pullback

Let `f : X ⟶ Y` be a finite flat morphism of schemes whose fibre rank
`f.finrank y` (Mathlib, `Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`) equals a
constant `d` for every `y : Y`. This module defines a `Γ(Y, V)`-linear trace

`localTrace f M hV : Γ(f_* f^* M, V) →ₗ[Γ(Y, V)] Γ(M, V)`

over the affine opens `V` of `Y` on which `Γ(X, f⁻¹V)` is a free `Γ(Y, V)`-module, for
every quasi-coherent module `M` on `Y`. It proves two facts:

- a pulled-back section `m` goes to `d • m`;
- the trace commutes with restriction to basic opens.

The proof module `FiniteFlatCohomologyRetractProof` glues these local traces into a
morphism `f_* f^* M ⟶ M`. All declarations are in the namespace
`Langlands.Scheme.Modules`. `Γ(X, f⁻¹V)` carries the `Γ(Y, V)`-algebra structure
`(f.app V).hom.toAlgebra`.

## Algebra

- `free_of_isLocalizedModule_of_free`: let `f : M →ₗ[R] Mₛ` be a localization of `M`
  at `S` (`IsLocalizedModule S f`), and let `Rₛ` be a localization of `R` at `S` that
  acts on `Mₛ` compatibly. If the standard localization `LocalizedModule S M` is free
  over `Localization S`, then `Mₛ` is free over `Rₛ`. Proof: transport a basis
  through `IsLocalizedModule.iso` and `IsLocalization.algEquiv`, then extend scalars
  with `LinearEquiv.extendScalarsOfIsLocalization`.

## Free charts and their trace

- `IsFreeChart f V`: `V` is affine and `Γ(X, f⁻¹V)` is a free `Γ(Y, V)`-module.
- `chartTrace f V : Γ(X, f⁻¹V) →+ Γ(Y, V)`: Mathlib's `Algebra.trace Γ(Y, V)
  Γ(X, f⁻¹V)`, as an additive map. `chartTrace_app_mul` records its
  `Γ(Y, V)`-linearity: `tr(f.app V r * a) = r * tr(a)`.
- `rankAtStalk_chart`: for affine `V`, the rank of `Γ(X, f⁻¹V)` at every prime of
  `Γ(Y, V)` (Mathlib's `Module.rankAtStalk`) is `d`. Mathlib's
  `IsOpenImmersion.isPullback` shows that the square formed by
  `Spec.map (f.app V)`, the charts `fromSpec` and `f` is a pullback. Then
  `Scheme.Hom.finrank_of_isPullback` and `Scheme.Hom.finrank_SpecMap_eq_finrank`
  identify the rank with `f.finrank` at the image point, which is `d`.
- `chartTrace_one`: on a free chart, `chartTrace f V 1 = d`. On a nonzero ring the
  free rank is the rank at any prime (`Module.rankAtStalk_eq_finrank_of_free`), and
  `Algebra.trace_algebraMap` gives `tr(1) = rank • 1`.
- `isLocalization_preimage_basicOpen`: for affine `V` and `g : Γ(Y, V)`,
  `Γ(X, f⁻¹ D(g))` is the localization of `Γ(X, f⁻¹V)` at the powers of the image of
  `g`. This is `IsAffineOpen.isLocalization_of_eq_basicOpen` with
  `Scheme.Hom.preimage_basicOpen`.
- `chartTrace_basicOpen`: on a free chart, the trace commutes with restriction to
  `D(g)`. This is Mathlib's `Algebra.trace_localization`, applied with the scalar
  towers `Γ(Y, V) → Γ(X, f⁻¹V) → Γ(X, f⁻¹ D(g))` and
  `Γ(Y, V) → Γ(Y, D(g)) → Γ(X, f⁻¹ D(g))`. The second tower commutes by
  `Scheme.Hom.map_appLE`.
- `IsFreeChart.basicOpen`: free charts are stable under basic opens. The basis of
  `Γ(X, f⁻¹V)` localizes to a basis of `Γ(X, f⁻¹ D(g))` over `Γ(Y, D(g))`
  (`Module.Basis.localizationLocalization`).
- `exists_isFreeChart`: every point `y` lies in a free chart. Take an affine
  `V ∋ y`. There, `Γ(X, f⁻¹V)` is finite (`Scheme.Hom.finite_app`) and flat
  (`Scheme.Hom.flat_appLE`) over `Γ(Y, V)`, with constant rank `d`
  (`rankAtStalk_chart`). Mathlib's
  `Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant` gives `a` outside the
  prime of `y` such that the localization at `a` is free. That localization is
  `Γ(X, f⁻¹ D(a))` by `isLocalization_preimage_basicOpen`, so
  `free_of_isLocalizedModule_of_free` shows that `D(a)` is a free chart. It contains
  `y` by `IsAffineOpen.fromSpec_preimage_basicOpen` and
  `IsAffineOpen.fromSpec_primeIdealOf`.

## The local trace on sections of `f_* f^* M`

From here on `M` is a quasi-coherent module on `Y`.

- `tensorTrace f M V`: the additive map `Γ(X, f⁻¹V) ⊗_{Γ(Y, V)} Γ(M, V) → Γ(M, V)`,
  `a ⊗ m ↦ chartTrace f V a • m`. The tensor product is over `f.appLE V (f⁻¹V) le_rfl`.
  It is defined by `TensorProduct.lift` of a bilinear map, whose balancing uses
  `chartTrace_app_mul`. `tensorTrace_tmul` is its value on pure tensors.
  `tensorTrace_smul` states `tensorTrace (f.app V r • z) = r • tensorTrace z`.
- `pullbackTensorEquiv f M hV` (for `IsAffineHom f` and affine `V`): the
  `Γ(X, f⁻¹V)`-linear equivalence given by the bijection `pullbackTensorMap f M`
  (module `PullbackAffineSections`; `f⁻¹V` is affine because `f` is affine).
  `pullbackTensorEquiv_apply` says it applies `pullbackTensorMap`.
- `localTrace f M hV`: `tensorTrace` composed with the inverse of
  `pullbackTensorEquiv`. Sections of `f_* f^* M` over `V` are by definition sections
  of `f^* M` over `f⁻¹V`, and `Γ(Y, V)` acts through `f.app V`. So `localTrace` is
  `Γ(Y, V)`-linear by `tensorTrace_smul`.
- `localTrace_pullbackTensorMap`: `localTrace (pullbackTensorMap z) = tensorTrace z`.
- `localTrace_smul_sectionPullbackLE`:
  `localTrace (a • (f^* m)|_{f⁻¹V}) = chartTrace f V a • m`.
- `localTrace_sectionPullback`: on a free chart,
  `localTrace f M hV.1 (sectionPullback f M V m) = d • m`. Write the pulled-back
  section as `pullbackTensorMap (1 ⊗ m)` and use `chartTrace_one`.
- `localTrace_basicOpen`: on a free chart `V` and for `g : Γ(Y, V)`, the local trace
  on `D(g)` of the restriction of `z` equals the restriction of the local trace of
  `z`. Since `pullbackTensorMap` is surjective, `z` comes from a tensor. By additivity
  it suffices to treat `z = a • (f^* m)|_{f⁻¹V}`. Its restriction to `f⁻¹ D(g)` is
  `a|_{f⁻¹D(g)} • (f^* (m|_{D(g)}))|_{f⁻¹ D(g)}` (`Scheme.Modules.map_smul`,
  `map_sectionPullbackLE`, `sectionPullbackLE_restrict`). Both sides then reduce to
  `tr(a)|_{D(g)} • m|_{D(g)}`, by `localTrace_smul_sectionPullbackLE` and
  `chartTrace_basicOpen`.

## Provenance and scope

This is an internal helper for proof task `f2728a31-103a-4d50-ae2d-6cb3f9ce05a9`. It is
the standard trace of a finite locally free algebra, applied on an affine basis on
which `f_* O_X` is free. No literature is cited for it. Everything is built from pinned
Mathlib (commit `5ed2965256430c3649e86755f9576b54eca72435`: `Algebra.trace`,
`Algebra.trace_localization` in `Mathlib/RingTheory/Localization/NormTrace.lean`,
`Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant` in
`Mathlib/RingTheory/Flat/LocallyFree.lean`, and the `finrank` API in
`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`) and from the module
`PullbackAffineSections`. The hypotheses are the instances `[IsFinite f]`, `[Flat f]`
and `[IsAffineHom f]` where needed, the constant rank `hd : ∀ y, f.finrank y = d`, and
`[M.IsQuasicoherent]`. Local finite presentation is not used.
