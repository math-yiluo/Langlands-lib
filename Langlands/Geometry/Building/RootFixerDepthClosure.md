# Root-fixer depths for affine-closure-ordered subsets

This is an internal consequence of `BoundedRootFixerFiltration` and elementary
topology and order theory. It supplies the depth comparison needed to compare
actual root-filtration models in the kernel argument. It constructs no models
and proves no geometric property of a special-fibre kernel.

Fix a field `k`, an affine group scheme `G`, a monomorphic inclusion
`i : S → G` from a commutative group scheme, and supplied
`D : KPApartmentData i ω`. All closures in this module use exactly the initial
topology

```text
⨅ f : D.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance.
```

`D.affineFunctionalTopology` names this topology for arbitrary supplied KP
apartment data. The theorem signatures retain the displayed formula, so they
apply directly to the existing host hypothesis by definitional equality.
Every real affine functional is continuous. No topology on `k`, discrete
valuation, or extra building axioms are required. The topology agrees with the
formula used in `UnramifiedModelKernelStatement`. These helpers apply directly
to its supplied apartment data; the existing closure helpers in `ModelFamily`
instead take `ValuationBuildingData`.

For subsets `Ω ⊆ closure Ω'`, the module proves:

- `nonempty_of_nonempty_subset_affineClosure`: if `Ω` is nonempty, then `Ω'`
  is nonempty. The proof uses nonemptiness of the closure and the fact that the
  closure of the empty set is empty.
- `bddAbove_affineImage_of_subset_affineClosure`: if a given real affine
  functional `f` is bounded above on `Ω'`, it is bounded above on `Ω`.
  Continuity puts `f '' Ω` inside `closure (f '' Ω')`, and closure preserves
  upper bounds in `ℝ`. Applying this separately to each `f` transfers affine
  boundedness.
- `rootFixerDepth_le_of_subset_affineClosure`: for a relative root `a` and
  any reference point `x`, if `Ω` is nonempty and the values
  `-D.affineFunctional a x 0 y` for `y ∈ Ω'` are bounded above, then
  `D.rootFixerDepth a x Ω ≤ D.rootFixerDepth a x Ω'`. The upper-bound
  hypothesis concerns just this one functional; full affine boundedness is
  unnecessary. The proof makes the right-hand supremum an upper bound on the
  threshold image of `Ω'`, carries that same upper bound to its closure, and
  uses continuity and the least-upper-bound inequality on the nonempty
  threshold image of `Ω`.
- `rootFixer_le_of_subset_affineClosure`: if `Ω` is nonempty and every real
  affine functional is bounded above on `Ω'`, then
  `D.rootFixer a Ω' ≤ D.rootFixer a Ω`. The preceding helpers supply the
  boundedness and nonemptiness for both sets. The proof rewrites both actual
  root fixers as single filtration levels with
  `rootFixer_eq_filtration_of_bounded`, then applies antitonicity of the
  filtration to the depth comparison.

The supremum argument uses no extremal point of either subset. In particular,
the comparison remains valid when the closure contains points absent from
`Ω'`. The reference point `x` need not belong to either subset.
