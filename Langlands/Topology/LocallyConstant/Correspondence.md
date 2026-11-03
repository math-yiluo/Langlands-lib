# Actual fibers and cartesian reindexing for compact-function correspondences

This is internal finite-sum infrastructure for the proper-pullback and finite-covering-trace construction. It uses the existing literal `fiberSum` from `CoveringTrace` and Mathlib's `IsPullback` in the category of types. It does not assert a theorem from Harris or Berkovich.

The spaces share universe `u`; additive commutative group coefficients have independent universe `w` and carry no topology. All fibers are the actual subtype `q ⁻¹' {y}`, including the empty fiber. A `Finite` instance is converted to a finite enumeration only to define the sum; its value is independent of that enumeration.

`fiberSum_comap` proves

```text
fiberSum q (f ∘ q) y = Nat.card (q ⁻¹' {y}) • f y.
```

The proof replaces each summand by `f y` using its original fiber equation, then evaluates the finite constant sum. This is the unnormalized degree law; the degree may vary with `y` and is never inverted.

For a square `a : S → X`, `b : S → Y`, `q : X → Z`, `p : Y → Z`, the hypothesis is literally

```text
IsPullback (↾a) (↾b) (↾q) (↾p).
```

`pullbackFiberEquiv` maps the original fiber of `b` over `y` to the original fiber of `q` over `p y` by `s ↦ a s`. The commutative square supplies membership; the uniqueness and existence properties of the actual limiting square supply injectivity and surjectivity. Its application formula is definitional. `finite_pullback_fiber` transfers finiteness through this equivalence.

`fiberSum_baseChange` reindexes the finite sum through that equivalence and proves

```text
fiberSum b (f ∘ a) y = fiberSum q f (p y).
```

The sum equality is proved from cartesianness, rather than supplied as compatibility data. Both finite-fiber instances are explicit in this lemma; the preceding finiteness result can discharge the base-changed instance.

`isPullback_prodSubtype` gives an actual instance of the geometric input: Mathlib's constructed limit cone on the product subtype `{(x,y) | q x = p y}`. This is an underlying-type pullback construction, with no topology or action asserted for that subtype here.

`fiberSum_pullback_comp` treats a second trace map `d : T → Z` and a cartesian square with projections `e : W → S`, `f : W → T` over `b : S → Y` and `c : T → Y`. It proves that the trace of `s ∘ e` along `d ∘ f` equals the trace along `d` of `t ↦ fiberSum b s (c t)`. The proof first uses the previously constructed sigma decomposition of composite fibers, then applies `fiberSum_baseChange` at each `t`. All fibers being summed, including the composite fibers, have explicit finiteness instances.

Topology, continuous actions, properness and covering hypotheses enter the representation and rational-spectrum layers. This file constructs no analytic etale trace, sheaf-derived comparison, or Shimura fiber product.
