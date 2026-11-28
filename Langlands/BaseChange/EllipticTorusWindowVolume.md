# Window volumes of elliptic centralizers and Weil's formula on the window

Lean module: `Langlands.BaseChange.EllipticTorusWindowVolume`.

Let `F` be a nonarchimedean local field, `n > 0`, `G = GL_n(F)` and
`D = degreeWindow (determinantOrder F n) n 0` the determinant window `0 ≤ ord_F(det g) < n` of
`Langlands.BaseChange.CentralQuotientWindowMeasure`. For a subgroup `H` of `G` and a measure `μH`
on `H`, the window volume is

`subgroupWindowVolume H μH = μH { h : h ∈ D }`.

For the centralizer `T` of a regular elliptic element, `T ∩ D` is a fundamental domain for the
powers of the scalar `ϖ` in `T`, and `T` is the product of the scalars with a compact set (the
compactness of `T / Z`, in the form proved below). So the window volume is positive and finite. It is the factor that converts Weil's formula for `T \ G` into a formula on the window of
`G`.

## Centralizers of regular elliptic elements

- `scalar_mem_glCentralizer`: scalar matrices lie in every centralizer.
- The private lemma `isUnit_of_commute_regularElliptic`: a nonzero matrix commuting with a
  regular elliptic `g` is invertible. Such a matrix is a polynomial in `g`
  (`regularCyclicBasis`, `exists_sum_pow_of_commute`), hence the image under
  `charpolyRootEvaluation` of a nonzero element of the field `F[X]/(charpoly g)`.
- `exists_isCompact_scalar_mul_glCentralizer`: for regular elliptic `g` there is a compact
  `K ⊆ glCentralizer g` with `glCentralizer g = Fˣ · K`. The set `K` consists of the centralizing
  matrices with entries of valuation at most `1` and some entry equal to `1`. It is compact as a
  closed subset of the compact product of unit balls, all of whose points are invertible by the
  previous lemma. An element `x` of the centralizer is brought into `K` by dividing by an entry
  of largest valuation.

## Window volumes

- `measure_mul_mem_window_eq`: for a left-invariant `μH` on a subgroup `H` containing the center,
  every right translate `{h : h x ∈ D}` of the window has measure `subgroupWindowVolume H μH`. Both
  sets are degree windows of length `n` of `h ↦ ord(det h)` on `H`, and the scalar `ϖ ∈ H` has
  degree `n` (`measure_inter_degreeWindow_eq`).
- `subgroupWindowVolume_pos`: positive for an open-positive measure, since `H ∩ D` is an open
  neighbourhood of `1` in `H`.
- `subgroupWindowVolume_lt_top`: finite for a measure that is finite on compacts when
  `H = glCentralizer g` with `g` regular elliptic. With `K` as above and the compact set `B` of
  `exists_isCompact_scalar_of_mem_window` for `K`, the set `H ∩ D` lies in the compact image of
  `B × K` under `(a, k) ↦ a k`.

## Weil's formula on the window

`measure_preimage_inter_window_eq`: let `H` be a closed subgroup of `G` containing the center,
`μG` a measure on `G` finite on compacts, `μH` a left- and right-invariant measure on `H` finite
on compacts, and `ν` a measure on `H \ G` compatible with `μG` and `μH` (`IsCompatible`, Weil's
quotient integration formula). Then for every measurable set `C` of cosets,

`μG (π⁻¹(C) ∩ D) = subgroupWindowVolume H μH · ν C`,

where `π : G → H \ G` is the coset map. The proof writes the left side as a `μG`-integral of an
indicator. `IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal` turns it into the
`ν`-integral of the average `Hx ↦ ∫_H 1_{π⁻¹(C) ∩ D}(h x) dμH(h)`. Since `π(h x) = π(x)`, this
average is `1_C(Hx) · μH {h : h x ∈ D}`, and `measure_mul_mem_window_eq` evaluates the last
factor as the window volume.

These are derived steps: the compactness of `Z \ T` for an elliptic torus `T`, and Weil's formula
for the quotient `T \ G` (for instance Henniart–Lemaire 2011, II.2.10, where the orbital
integrals are taken for the quotient measure `dg / dγ_T`), restricted to the determinant window.
