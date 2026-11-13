# Reduced trace of a central simple algebra

Authors: Worker 118.

Module `Langlands.Algebra.CentralSimpleReducedTrace`, namespace `Langlands.CentralSimple`.
Throughout, `K A : Type u` share an arbitrary universe, `K` is a field and `A` is a
finite-dimensional central simple `K`-algebra (`[Ring A] [Algebra K A] [FiniteDimensional K A]
[Algebra.IsCentral K A] [IsSimpleRing A]`). The characteristic of `K` is unrestricted, including
characteristic 2.

## Definitions

- `reducedTraceValue K A a : K` is

  ```text
  -(reducedCharpoly K A a).coeff (reducedDegree K A - 1),
  ```

  minus the coefficient of degree `d - 1` of the Library's canonical reduced characteristic
  polynomial (`Langlands.Algebra.ReducedCharpoly`), where `d = reducedDegree K A` is the
  positive reduced degree (`d² = dim_K A`).
- `reducedTraceLinear K A : A →ₗ[K] K` packages this value as a `K`-linear map; this is the
  reduced trace `Trd`. `reducedTraceLinear_apply` unfolds it (by `rfl`).
- `reducedTracePairing K A : A →ₗ[K] A →ₗ[K] K` is the `K`-bilinear pairing
  `(b, a) ↦ Trd (b * a)`, built as `(LinearMap.mul K A).compr₂ (reducedTraceLinear K A)`;
  `reducedTracePairing_apply` unfolds it (by `rfl`).

## Normalization

`algebraMap_reducedTraceLinear` (and its value-level form `algebraMap_reducedTraceValue`) proves
that for every field `L : Type uL` in an arbitrary independent universe, every `[Algebra K L]`
and every actual splitting chart

```text
e : L ⊗[K] A ≃ₐ[L] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L,
```

```text
algebraMap K L (Trd a) = (e (1 ⊗ₜ a)).trace.
```

The proof maps the coefficient to `L` (`Polynomial.coeff_map`), rewrites with the Library's
`reducedCharpoly_map_chart`, which identifies the mapped reduced characteristic polynomial with
the characteristic polynomial of `e (1 ⊗ₜ a)`, and finishes with Mathlib's
`Matrix.trace_eq_neg_charpoly_coeff` (the trace of an `n × n` matrix is minus the coefficient of
degree `n - 1` of its characteristic polynomial).

## Linearity

Additivity and `K`-homogeneity are proved after the injective map `K → L` for the Library's
constructed finite Galois splitting chart `finiteGaloisSplittingChart K A` (over
`finiteGaloisSplittingField K A`), so no splitting field is supplied as a premise. Under the
chart the statements become additivity and homogeneity of the matrix trace, since
`a ↦ e (1 ⊗ₜ a)` is additive and `e (1 ⊗ₜ t • a) = algebraMap K L t • e (1 ⊗ₜ a)`.

## Remarks

- This is not the trace of the regular representation `a ↦ tr_K(x ↦ a x)`, which equals
  `d · Trd a` and vanishes identically when the characteristic divides `d` (for example a
  quaternion algebra in characteristic 2).
- The name avoids `reducedTrace`, which is already used by the division-algebra-specific
  `Langlands.CentralDivision.reducedTrace` in `Langlands.Algebra.QuaternionCommutator` (whose
  namespace opens `Langlands.CentralSimple`).

## Provenance

Internal. The reduced trace is the standard notion (Tits 1968, §2.4, uses "la trace réduite"
`Trd` of a central simple algebra); this module derives it from the existing
`reducedCharpoly` and its chart comparison, as suggested by Task 5551, and introduces no new
assertion from external literature.
