# The adelic group as a product at one finite place

Module `Langlands.TraceFormula.IsotypicTrace.PlaceProduct`. Internal to the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.
It carries out the first step of the reduction: the product decomposition, the normalization
of Haar measures, and integrability of the away factor.

## Setting

`F` is a number field, `G` an affine group scheme over `F` (locally of finite type where
measures are used), and `v` a finite place. `G(F_v) = PlaceGroupPoints F G (.inr v)` carries a
Borel measurable structure given as instance binders, as in the target statement.

## Results

* `awaySubgroup F G v`: the kernel of `atPlace F G (.inr v)`, i.e. the adelic points with
  trivial component at `v`. It is closed (`isClosed_awaySubgroup`), and its elements commute with
  `ofPlace F G (.inr v) y` (`ofPlace_mul_comm`; proved place by place with `ext_atPlace`).
* `exists_split`: every `g` is `ofPlace (g_v) * c` with `c = ofPlace(g_v)⁻¹ g` in the away
  subgroup, commuting with the image of `ofPlace`.
* `placeSplitting F G v : G(F_v) × awaySubgroup F G v ≃ₜ* G(𝔸_F)`, `(y, h) ↦ ofPlace y * h`, with
  inverse `g ↦ (g_v, ofPlace(g_v)⁻¹ g)`. Both directions are continuous since `ofPlace` and
  `atPlace` are.
* Instances on the away subgroup: local compactness (closed subset) and second countability
  (subspace of the second countable `G(𝔸_F)`).
* `exists_awayHaar`: for Haar measures `μv` on `G(F_v)` and `ν` on `G(𝔸_F)`, there is a Haar
  measure `νH` on the away subgroup with `map placeSplitting (μv.prod νH) = ν`. The pullback of
  `ν` is a left Haar measure on the product, hence a positive multiple of `μv.prod haar`
  (`isMulLeftInvariant_eq_smul`); `νH` absorbs the constant. This repeats the argument of the
  Library's `productHaarNormalization` but needs only left invariance of `ν`, since the target
  assumes only `ν.IsHaarMeasure`.
* `integral_split_eq`. Let `π` be a norm-preserving action of `G(𝔸_F)` on a Hilbert space with
  continuous orbits, `fw` right invariant under `ofPlace (G(F_v))`, `fv ≠ 0` a Schwartz–Bruhat
  function, and `g ↦ fv (g_v) * fw g` integrable for `ν`. Then
  1. `fw` restricted to the away subgroup is `νH`-integrable: `fv` is nonzero on a nonempty open
     set of positive `μv`-measure (local constancy), and the slices of the integrable function
     `(y, h) ↦ fv y * fw h` are integrable for almost every `y`
     (`Integrable.prod_right_ae`, `exists_mem_of_measure_ne_zero_of_ae`);
  2. `∫ (fv (g_v) * fw g) • π g x ∂ν = ∫ fv y • π (ofPlace y) (∫ fw h • π h x ∂νH) ∂μv`, by
     change of variables along `placeSplitting` (`integral_map_equiv`), Fubini
     (`integral_prod`), and the identities `atPlace (ofPlace y * h) = y` and
     `fw (ofPlace y * h) = fw h`.
