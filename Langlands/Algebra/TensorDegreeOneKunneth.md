# A degree-one Künneth lemma for tensor products over a field

Author: Worker 727.

This module proves a purely linear-algebraic lemma about tensor products of vector spaces over
a field. It is a helper for the proof of
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement`, where `C₀ ⟶ C₁` and
`D₀ ⟶ D₁` are the first Čech differentials of the structure sheaves of `X` and `Y` for finite
affine covers. It contains no `sorry` and no new axioms.

## Main result

`Langlands.Algebra.TensorDegreeOneKunneth.exists_eq_of_degreeOne`:

```lean
theorem exists_eq_of_degreeOne (dC : C₀ →ₗ[K] C₁) (dD : D₀ →ₗ[K] D₁) (eC : C₀) (eD : D₀)
    (εC : C₀ →ₗ[K] K) (εD : D₀ →ₗ[K] K)
    (hC : ∀ x, dC x = 0 → ∃ a : K, x = a • eC)
    (hD : ∀ x, dD x = 0 → ∃ a : K, x = a • eD) (hdD : dD eD = 0)
    (hεC : εC eC = 1) (hεD : εD eD = 1)
    (h : C₁ ⊗[K] D₀) (v : C₀ ⊗[K] D₁)
    (hhv : dD.lTensor C₁ h = dC.rTensor D₁ v)
    (hv : TensorProduct.lid K D₁ (εC.rTensor D₁ v) ∈ LinearMap.range dD)
    (hh : TensorProduct.rid K C₁ (εD.lTensor C₁ h) ∈ LinearMap.range dC) :
    ∃ w : C₀ ⊗[K] D₀, dC.rTensor D₀ w = h ∧ dD.lTensor C₀ w = v
```

Here `K` is a field (`[Field K]`) and `C₀ C₁ D₀ D₁` are `K`-vector spaces. In words: let the
kernels of `dC` and `dD` be contained in the lines `K · eC` and `K · eD` (and `eD` lies in the
kernel of `dD`), and let `εC`, `εD` be linear forms with `εC eC = 1`, `εD eD = 1`. A pair
`(h, v)` with `h ∈ C₁ ⊗ D₀`, `v ∈ C₀ ⊗ D₁` satisfying the mixed condition
`(1 ⊗ dD) h = (dC ⊗ 1) v`, and whose images `(εC ⊗ 1) v ∈ D₁` and `(1 ⊗ εD) h ∈ C₁` are
boundaries, is the total differential `((dC ⊗ 1) w, (1 ⊗ dD) w)` of some `w ∈ C₀ ⊗ D₀`.

No assumption that `eC` lies in the kernel of `dC` is needed, and no condition on the second
differential of `D` is used.

## Provenance

This is an internal lemma. It is the degree-one part of the algebraic Künneth formula for the
tensor product of two complexes over a field, which the Stacks Project uses in its proof of
the Künneth formula for quasi-coherent cohomology (Stacks, Varieties, Lemma 0BED,
`lemma-kunneth`, `varieties.tex` lines 5441-5630 of the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). Only the part needed to show that a class of
`H¹(X ×_K Y, 𝒪)` killed on both axes is zero is proved here: the total-degree-one cocycles of
`C ⊗ D` in the two components `C₁ ⊗ D₀` and `C₀ ⊗ D₁` with boundary axis restrictions are
total coboundaries. In the application `eC = 1`, `eD = 1` (constants, since global functions
are constants), and `εC`, `εD` are evaluation at rational points.

## Proof

All tensor products are over `K`; flatness of every `K`-module (`Module.Flat` over a field) is
used through Mathlib's `Module.Flat.lTensor_exact` and `Module.Flat.rTensor_exact`.

1. **`v` is a boundary in the second factor.** Let `q : D₁ ⟶ D₁ / range dD` be the quotient
   map. Then `(dC ⊗ 1)((1 ⊗ q) v) = (1 ⊗ q)((1 ⊗ dD) h) = 0` by `hhv`
   (`rTensor_lTensor_comm`). The sequence `ker dC ⟶ C₀ ⟶ C₁` stays exact after tensoring, and
   `ker dC ⊆ K · eC`, so `(1 ⊗ q) v = eC ⊗ η` for some `η`
   (`exists_eq_tmul_of_rTensor_eq_zero`). Applying `lid ∘ (εC ⊗ 1)` gives
   `η = q(lid((εC ⊗ 1) v))` (`lid_rTensor_lTensor`, `hεC`), which is `0` by `hv`. So
   `(1 ⊗ q) v = 0`, and right exactness of the tensor product (`lTensor_exact` for the exact
   sequence `D₀ ⟶ D₁ ⟶ D₁ / range dD ⟶ 0`) gives `w₀` with `(1 ⊗ dD) w₀ = v`.
2. **Correcting the first component.** `h' = h - (dC ⊗ 1) w₀` satisfies `(1 ⊗ dD) h' = 0`,
   so `h' = γ ⊗ eD` for some `γ ∈ C₁` (`exists_eq_tmul_of_lTensor_eq_zero`). Write
   `rid((1 ⊗ εD) h) = dC c` by `hh`. Applying `rid ∘ (1 ⊗ εD)` to `h' = γ ⊗ eD` gives
   `γ = dC (c - rid((1 ⊗ εD) w₀))` (`rid_lTensor_rTensor`, `hεD`).
3. **Conclusion.** `w = w₀ + (c - rid((1 ⊗ εD) w₀)) ⊗ eD` works: `(dC ⊗ 1) w = (dC ⊗ 1) w₀ +
   γ ⊗ eD = h`, and `(1 ⊗ dD) w = v + (…) ⊗ dD eD = v` by `hdD`.

## Auxiliary results

All in namespace `Langlands.Algebra.TensorDegreeOneKunneth`, for vector spaces over a field
`K`:

- `rTensor_lTensor_comm f g t`: `f.rTensor Q (g.lTensor M t) = g.lTensor P (f.rTensor N t)`.
- `lid_rTensor_lTensor ε q t`: `lid (ε.rTensor P (q.lTensor M t)) = q (lid (ε.rTensor N t))`.
- `rid_lTensor_rTensor ε f t`: `rid (ε.lTensor P (f.rTensor N t)) = f (rid (ε.lTensor M t))`.
- `exists_eq_tmul_of_lTensor_eq_zero M d e he t ht`: if every element of `ker d` is a multiple
  of `e`, then every `t ∈ M ⊗ D₀` with `(1 ⊗ d) t = 0` has the form `γ ⊗ e`.
- `exists_eq_tmul_of_rTensor_eq_zero N d e he t ht`: the mirror statement, `t = e ⊗ η`.
