# Reduced-norm-one points through a matrix chart along a point of a splitting field

Let `K` be a field, `A` a finite-dimensional central simple `K`-algebra,
`L` a field over `K`, and `ε : L ⊗[K] A ≃ₐ[L] Matrix I I L` a splitting
chart indexed by a finite type `I`. This module transports the chart along
an arbitrary ring homomorphism `f : L → R` over `K` and along points of
`Spec L` over `Spec K`. It is an internal helper for the proof of
`SpecialLinearInnerFormNormOneStatement`.

## Chart along a ring homomorphism

* `chartAlong ε f hf : R ⊗[K] A →ₐ[R] Matrix I I R`, for a commutative
  `K`-algebra `R` and a ring homomorphism `f : L →+* R` with
  `f ∘ algebraMap K L = algebraMap K R` (hypothesis `hf`). It is the
  Library's `splittingMap ε R` for the `L`-algebra structure on `R`
  given by `f`. Taking `f` explicitly avoids fixing an `L`-algebra
  instance on `R`.
* `chartAlong_tmul`: on a pure tensor, `r ⊗ a ↦ r • (ε (1 ⊗ a)).map f`
  (definitional).
* `reducedNorm_eq_det_chartAlong`: the canonical reduced norm
  `reducedNorm K A R x` equals the determinant of `chartAlong ε f hf x`
  (the Library's `reducedNorm_eq_det_fintype`).
* `chartAlong_bijective`: the extended chart is bijective (it is the
  Library's `extendSplittingChart ε R`).
* `chartAlong_congr`: transport of the chart along an equality of the
  homomorphisms `f`.
* `chartAlong_naturality`: for a `K`-algebra homomorphism `g : R → S`,
  `chartAlong ε (g ∘ f) (base change of x along g) = (chartAlong ε f x).map g`.
* `chartUnitsEquiv ε f hf : reducedNormOne K A R ≃* SL I R`, the group
  isomorphism sending a reduced-norm-one unit to its chart image, with
  `chartUnitsEquiv_val`.

## Points over a point of `Spec L`

For a relative test scheme `V` over `Spec K` and a morphism
`s : V ⟶ ringTest K L` over `Spec K` (where `ringTest K L` is `Spec L`
over `Spec K`):

* `pointScalars s : L →+* Γ(V)`, the global-sections map of `s` composed
  with `Γ(Spec L) ≅ L`;
* `pointScalars_comp_algebraMap`: it is compatible with the `K`-algebra
  structure of `Γ(V)`;
* `pointScalars_comp`: for `t : W ⟶ V`,
  `pointScalars (t ≫ s) = t^* ∘ pointScalars s`;
* `pointScalars_comp_ringTestMap`: for `σ ∈ Gal(L/K)`,
  `pointScalars (s ≫ Spec σ) = pointScalars s ∘ σ`;
* `normOneChartPoints ε s : (V ⟶ normOne K A) ≃* SL I Γ(V)`, the composite
  of the Library's `CentralSimpleUnits.normOnePointsEquiv` with
  `chartUnitsEquiv ε (pointScalars s)`; `normOneChartPoints_val` gives its
  underlying matrix;
* `normOneChartPoints_naturality`: for `t : W ⟶ V`,
  `normOneChartPoints ε (t ≫ s) (t ≫ x)` is the image of
  `normOneChartPoints ε s x` under `t^*` on matrix entries.

## Proof

All statements are direct consequences of the Library's chart
infrastructure in `Langlands.Algebra.ReducedNormFiniteChart`
(`splittingMap`, `extendSplittingChart`, `reducedNorm_eq_det_fintype`) and
of `CentralSimpleUnits.normOnePointsEquiv` with its naturality. The inverse
of `chartUnitsEquiv` maps a determinant-one matrix through the inverse of
the bijective algebra map `chartAlong ε f hf` on units; the determinant
condition follows from `reducedNorm_eq_det_chartAlong`. Naturality of the
chart is checked on pure tensors, where both sides are
`g r • (ε (1 ⊗ a)).map (g ∘ f)`. The scalar-map identities follow from
functoriality of global sections and the naturality of `Γ(Spec R) ≅ R`
(`Scheme.ΓSpecIso_inv_naturality`).

The module states no result from external literature; it repackages the
Library's splitting charts in the form used by the main proof.
