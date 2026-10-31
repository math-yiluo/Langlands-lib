# Schwartz–Bruhat functions on products

Module `Langlands.HarmonicAnalysis.SchwartzBruhatProduct`. Author: Worker 1112.

`SchwartzBruhat X` is the Library space of compactly supported locally constant
complex functions (`Langlands.HarmonicAnalysis.Basic`). This module proves the
elementary closure properties needed to split full-matrix test functions into
products of block test functions.

## Definitions

- `SchwartzBruhat.tensor α β : SchwartzBruhat (X × Y)` is `(x, y) ↦ α x * β y`.
  Local constancy is composition with the projections; its topological support
  lies in `tsupport α ×ˢ tsupport β`, which is compact.
- `SchwartzBruhat.compLeftInverse f g π`: for `f ∈ SchwartzBruhat X`, a continuous
  `g : Y → X` with a continuous left inverse `π` (`π (g y) = y`) and `Y` Hausdorff,
  the composite `y ↦ f (g y)`. Its support is contained in `π '' tsupport f`, which
  is compact; this is how test functions are restricted to closed linear subspaces
  such as upper block-triangular matrices.
- `SchwartzBruhat.sliceSnd f x : SchwartzBruhat Y` is `y ↦ f (x, y)` (an instance of
  `compLeftInverse` with `π = Prod.snd`).
- `SchwartzBruhat.partialIntegral f ν : SchwartzBruhat X` is
  `x ↦ ∫ y, f (x, y) dν` for a measure `ν` finite on compact sets (Borel-type
  `OpensMeasurableSpace Y`, both spaces Hausdorff). It is Schwartz–Bruhat because,
  by the tensor expansion below, it equals the finite combination
  `∑ j, (∫ β j dν) • α j`.

## Theorems

- `isLocallyConstant_curry`: the function-valued map `x ↦ (y ↦ f (x, y))` is
  locally constant. Proof: for fixed `x`, local constancy of `f` at each `(x, y)`
  and compactness of `Prod.snd '' tsupport f` give, by
  `IsCompact.eventually_forall_of_forall_eventually`, a neighbourhood of `x` on
  which `f (x', y) = f (x, y)` for all `y` in that compact set; outside it both
  values vanish.
- `hasCompactSupport_curry`: that map has compact support, contained in the compact
  set `Prod.fst '' tsupport f` (Hausdorff `X`).
- `exists_tensor_expansion`: every `f ∈ SchwartzBruhat (X × Y)` (Hausdorff factors)
  satisfies `f (x, y) = ∑ j, α j x * β j y` for finitely many
  `α j ∈ SchwartzBruhat X`, `β j ∈ SchwartzBruhat Y`, chosen before `x` and `y`.
  Proof: the Library's `exists_finite_schwartz_expansion` applied to the curried
  family gives `f (x, y) = ∑ j, φ j x * f (r j, y)`; take `α j = φ j` and
  `β j = sliceSnd f (r j)`.
- `SchwartzBruhat.integrable`: Schwartz–Bruhat functions are integrable for every
  measure finite on compact sets (continuous with compact support).

The slice is named `sliceSnd` because `Langlands.HarmonicAnalysis.SchwartzBruhat.slice`
is already the middle-coordinate slice of `Distribution.CharacterAverage`; the
two modules can be imported together.

## Scope

These are internal topological facts about Schwartz–Bruhat functions used for the
two-block Godement–Jacquet analytic induction (Godement–Jacquet 1972, Theorem 3.4,
printed 40–41, where the restriction of a test function to the parabolic is
integrated over the unipotent radical and written as a sum of products). No
measure normalization or representation theory is involved.
