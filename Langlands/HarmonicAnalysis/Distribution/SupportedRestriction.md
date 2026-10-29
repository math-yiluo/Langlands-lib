# Supported-distribution descent on closed subsets and relatively closed pieces

This module, in namespace `Langlands.HarmonicAnalysis.Distribution`,
constructs three complex linear operations on algebraic distributions
together with their evaluation, inverse and uniqueness laws. It imports the
published modules `Distribution.Subspace` and
`Distribution.ClosedSupportedDescentProof` by Lean name and changes neither
them nor anything they import.

Throughout, `X : Type u` lies in an arbitrary universe. Every subset carries
Mathlib's induced subtype topology; a subset of a subtype `U` carries the
subtype topology of `U`. `Distribution Y` is the published full complex
algebraic dual of `SchwartzBruhat Y`, with no topology or continuity
condition. `supportedOn Z` is the published submodule of those `T` with
`T f = 0` for every test function `f` such that `f z = 0` for all `z ∈ Z`
(pointwise-annihilator support); `Z` need not be closed.

## 1. The closed supported equivalence

Assume `[T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]`
and `hZ : IsClosed Z`.

```
closedPushforwardSupportedEquiv hZ : Distribution Z ≃ₗ[ℂ] supportedOn Z
```

is `LinearEquiv.ofBijective (closedPushforwardSupported hZ) h`, where the
bijectivity proof `h` is the published theorem
`closedSupportedDescent X Z hZ` (whose type is the published
`ClosedSupportedDescentStatement.{u}`). Closed test-function restriction and
its surjectivity are not reproved, and no surjectivity or bijectivity premise
is added. Its forward map is, definitionally, the published
`closedPushforwardSupported hZ`. Its inverse
`(closedPushforwardSupportedEquiv hZ).symm` is the chosen closed descent.
Mathlib's `LinearEquiv.ofBijective` builds this inverse from the bijection.
It is complex linear because it is the inverse of a linear equivalence.

Proved laws (all `rfl` or direct consequences of the equivalence):

- `closedPushforwardSupportedEquiv_toLinearMap`: the underlying linear map
  equals `closedPushforwardSupported hZ`.
- `closedPushforwardSupportedEquiv_apply`: `e D = closedPushforwardSupported hZ D`.
- `coe_closedPushforwardSupportedEquiv`: the ambient coercion
  `(e D : Distribution X)` is the actual `closedPushforward hZ D`, i.e.
  `f ↦ D (restrictClosed hZ f)`.
- `closedPushforwardSupportedEquiv_symm_apply_apply`: `e.symm (e D) = D`.
- `closedPushforwardSupportedEquiv_apply_symm_apply`: `e (e.symm T) = T`.
- `closedPushforward_closedPushforwardSupportedEquiv_symm`:
  `closedPushforward hZ (e.symm T) = (T : Distribution X)`, obtained by
  taking the subtype value of the previous law.
- `closedPushforwardSupportedEquiv_symm_apply_restrictClosed`:
  `e.symm T (restrictClosed hZ f) = T f` for every `f : SchwartzBruhat X`,
  by rewriting with `closedPushforward_apply` and the previous law.
- `eq_closedPushforwardSupportedEquiv_symm_iff` (uniqueness):
  `D = e.symm T ↔ closedPushforward hZ D = T`. By
  `LinearEquiv.eq_symm_apply`, the left side is `e D = T`, and equality in the
  submodule is equality of the ambient coercions.

Here `e` abbreviates `closedPushforwardSupportedEquiv hZ`, `D : Distribution Z`
and `T : supportedOn Z`.

## 2. Open restriction between supported submodules

Assume only `[T2Space X]`, the hypothesis that the published `restrictOpen`
needs. Let `hU : IsOpen U` and let `Z : Set X` be arbitrary (no closedness
assumption). Write `Z_U = (Subtype.val : U → X) ⁻¹' Z`.

`restrictOpen_mem_supportedOn hU hD` shows: if `D ∈ supportedOn Z`, then
`restrictOpen hU D ∈ supportedOn Z_U`. Let `f : SchwartzBruhat U` vanish at
every point of `Z_U`. By `restrictOpen_apply`, the value is
`D (extendZero hU f)`, so it suffices by the defining condition of
`supportedOn Z` to show that `extendZero hU f` vanishes at each `z ∈ Z`.
There are exactly the two zero-extension cases. If `z ∈ U`, then
`extendZero_apply_of_mem` gives the value `f ⟨z, _⟩`, which is zero because
`⟨z, _⟩ ∈ Z_U`. If `z ∉ U`, then `extendZero_apply_of_not_mem` gives zero.
No other property of distributions or supports is used.

```
restrictOpenSupported hU Z : supportedOn Z →ₗ[ℂ] supportedOn Z_U
```

is `restrictOpen hU` precomposed with the inclusion `(supportedOn Z).subtype`
and corestricted (`LinearMap.codRestrict`) to `supportedOn Z_U` by that
lemma. Its laws, both `rfl`:

- `coe_restrictOpenSupported`:
  `(restrictOpenSupported hU Z D : Distribution U) = restrictOpen hU (D : Distribution X)`;
- `restrictOpenSupported_apply`: its value at `f : SchwartzBruhat U` is
  `(D : Distribution X) (extendZero hU f)`.

No local compactness or total disconnectedness is assumed for this operation.

## 3. Descent to the relatively closed piece of an open set

Assume again `[T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]`.
Let `hU : IsOpen U`, `Z : Set X` arbitrary, and
`hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z)`, i.e. `Z_U` is closed in `U`.
The space `U` is Hausdorff and totally disconnected by Mathlib's subtype
instances. It is locally compact by `IsOpen.locallyCompactSpace hU`, which
the definition and proofs supply locally with `haveI`. No global instance
is added. The closed equivalence of Section 1 is applied in the actual space
`U`, with the closed subset `Z_U`.

```
descendInOpen hU hZU : supportedOn Z →ₗ[ℂ] Distribution Z_U
descendInOpen hU hZU =
  (closedPushforwardSupportedEquiv hZU).symm.toLinearMap ∘ₗ restrictOpenSupported hU Z
```

This composition is the definition. It is recorded by `rfl` as
`descendInOpen_eq_comp` and pointwise as `descendInOpen_apply`. Proved laws:

- `closedPushforward_descendInOpen` (pushforward characterization):
  `closedPushforward hZU (descendInOpen hU hZU D) = restrictOpen hU (D : Distribution X)`.
  This is `closedPushforward_closedPushforwardSupportedEquiv_symm` in `U`
  applied to `restrictOpenSupported hU Z D`, whose coercion is
  `restrictOpen hU D` by definition.
- `descendInOpen_apply_restrictClosed`: for `f : SchwartzBruhat U`,
  `descendInOpen hU hZU D (restrictClosed hZU f) = D (extendZero hU f)`,
  by evaluating the previous identity at `f` with `closedPushforward_apply`
  and `restrictOpen_apply`.
- `eq_descendInOpen_iff` (uniqueness): for every
  `E : Distribution Z_U`, `E = descendInOpen hU hZU D` if and only if
  `closedPushforward hZU E = restrictOpen hU (D : Distribution X)`. This is
  `eq_closedPushforwardSupportedEquiv_symm_iff` in `U`.

Here `D : supportedOn Z`. The output lives on the nested subtype
`Z_U ⊆ U` exactly as written. No identification with `U ∩ Z` presented as
a subset of `X` is made or needed.

## Scope

There is no countability, global compactness, nonemptiness, manifold, group,
measure, continuity-of-functional or support-equivalence premise. In
particular `X`, `U`, `Z` and `Z_U` may be empty. The input of both descent
operations is the supported submodule `supportedOn Z`; no restriction map
from every ambient distribution to a closed or locally closed subset is
exported. The module makes no claim that pointwise-annihilator support agrees
with any topological notion of distribution support. It proves no
geometric, equivariance, filtration, orbit-vanishing, Whittaker invariance
or multiplicity-one statement. The use for a closed filtration layer `Z`
and the open complement `U` of a lower layer is only an intended
application.

## Provenance

These are internal constructions. They compose the published Library
objects `closedPushforwardSupported`, `closedPushforward`,
`restrictOpen`, `supportedOn`, `SchwartzBruhat.restrictClosed` and
`SchwartzBruhat.extendZero` (module `Distribution.Subspace`) with the
published bijectivity theorem `closedSupportedDescent`
(module `Distribution.ClosedSupportedDescentProof`). The only Mathlib inputs
are `LinearEquiv.ofBijective`, `LinearMap.codRestrict`,
`IsOpen.locallyCompactSpace` and elementary equivalence lemmas. No
literature statement is transcribed. The motivating descent remark after
Shalika (1974), Lemma 1.15, and its relation to the pointwise support
convention are documented in the unchanged
[ClosedSupportedDescentStatement](ClosedSupportedDescentStatement.md).
Worker 976 wrote this module, following the construction route laid out in
its task specification (task `d7ce8c86-d4c3-4a77-a27e-6ff359fda383`).
