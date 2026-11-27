# Real traces of `F_∞`-linear maps

Module `Langlands.Global.InfiniteAdelicRealTrace`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. `F` is a number field, `F_∞ = InfiniteAdeleRing F
= Π_v F_v`, and each completion `F_v` carries the Library's pinned `RCLike` structure
`InfinitePlaceGroupPoints.completionRCLike F v`, the one used for the archimedean manifold
structures. `mult(v)` is Mathlib's `InfinitePlace.mult` (1 at real, 2 at complex places).

## Declarations

- `realAlgebra F : Algebra ℝ (InfiniteAdeleRing F)`: the product of the `ℝ`-algebra structures
  of the completions. `realAlgebra_algebraMap`: its structure map is `realAdele F`, the
  diagonal map `r ↦ (r)_v` of `InfiniteAdelicTangentKernel`.
- `completion_I_eq_zero_iff`: for the pinned structure, `I = 0` in `F_v` exactly when `v` is
  real. If `I = 0` then `F_v ≅ ℝ` (`RCLike.realRingEquiv`), so a complex place would give a
  ring isomorphism `ℂ ≅ ℝ` (Mathlib's `ringEquivComplexOfIsComplex`), which is impossible since
  `-1` is not a square in `ℝ`. If `I ≠ 0` then `I² = -1`, which is impossible in
  `F_v ≅ ℝ` at a real place (`ringEquivRealOfIsReal`).
- `algebraTrace_completion`: `Tr_{F_v/ℝ}(z) = mult(v) · Re z`, from the previous theorem and
  `algebraTrace_of_I_eq_zero`, `algebraTrace_of_I_ne_zero` (module `RestrictScalarsTrace`).
- `algebraTrace_infiniteAdeleRing`: `Tr_{F_∞/ℝ}(x) = Σ_v mult(v) · Re (x_v)`, by
  `algebraTrace_pi`.
- `trace_restrictScalars_eq_sum`: for a finite free `F_∞`-module `M` with a compatible real
  structure (`IsScalarTower ℝ F_∞ M` for `realAlgebra F`) and an `F_∞`-linear endomorphism `f`,

  ```text
  tr_ℝ f = Σ_v mult(v) · Re ((tr_{F_∞} f)_v).
  ```

  This is `trace_restrictScalars` followed by `algebraTrace_infiniteAdeleRing`.

## Provenance

Internal. `F_∞` is a finite free `ℝ`-algebra with `Tr_{F_∞/ℝ} = Σ_v mult(v) · Re`; with the
transitivity of traces this computes real traces of `F_∞`-linear maps.
