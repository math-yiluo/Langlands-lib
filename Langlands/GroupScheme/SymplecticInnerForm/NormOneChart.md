# Norm-one involution isometries through a symplectic chart along a point of a splitting field

Let `K` be a field, `A` a `K`-algebra with an involution of the first kind
`τ`, `L` a field over `K`, and
`ε : L ⊗[K] A ≃ₐ[L] Matrix (I ⊕ I) (I ⊕ I) L` a splitting chart indexed by
`I ⊕ I` for a finite type `I`. The chart is assumed to carry `τ` to the
adjoint involution of the standard alternating matrix `J = Matrix.J I L`:

`he : ∀ x, ε (τ_L x) * J = J * (ε x)ᵀ`,

where `τ_L = τ.baseChange L`. This is the same identity as in
`HasStandardSymplecticSplitting`, but no finiteness or Galois condition on
`L` is needed here. The module is an internal helper for the proof of
`SymplecticInnerFormAntihermitianStatement`. It is the symplectic analogue
of `Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart` and uses that
module's `chartAlong` and `pointScalars`. All declarations are in the
namespace `Langlands.GroupScheme.SymplecticInnerForm`; `τ` is an implicit
argument determined by `he`.

## The involution through the extended chart

Let `R` be a commutative `K`-algebra and `f : L →+* R` a ring homomorphism
with `f ∘ algebraMap K L = algebraMap K R` (hypothesis `hf`). Write
`χ = SpecialLinearInnerForm.chartAlong ε f hf : R ⊗[K] A →ₐ[R] Matrix (I ⊕ I) (I ⊕ I) R`
and `J_R = Matrix.J I R`.

* `chartAlong_baseChange_mul_J ε he f hf x`:
  `χ (τ_R x) * J_R = J_R * (χ x)ᵀ` for every `x : R ⊗[K] A`, where
  `τ_R = τ.baseChange R`.
* `chartAlong_baseChange ε he f hf x`:
  `χ (τ_R x) = -(J_R * (χ x)ᵀ * J_R)`, i.e. `χ ∘ τ_R` is `M ↦ J Mᵀ J⁻¹`
  with `J⁻¹ = -J`.
* `mul_baseChange_eq_one_iff ε he f hf x`:
  `x * τ_R x = 1 ↔ χ x ∈ Matrix.symplecticGroup I R`, where Mathlib's
  symplectic group consists of the matrices `M` with `M * J * Mᵀ = J`.

## Points over a point of `Spec L`

Now let `A` be finite-dimensional, central and simple. Let `V` be a
relative test scheme over `Spec K` (not necessarily affine), and let
`s : V ⟶ ringTest K L` be a morphism over `Spec K`. Write `R_V` for the
`K`-algebra of global sections of `V`, and take `f = pointScalars s`.

* `rangeChartHom ε he s` is a monoid homomorphism from the points over `V`
  of the range of `normOneAmbientι τ` (a subgroup of the points of the
  algebra-unit group `CentralSimpleUnits.groupScheme K A`) to
  `Matrix.symplecticGroup I R_V`. It sends a point to the extended chart of
  its tensor unit under `FiniteAlgebraUnits.pointsEquiv`. Its underlying
  matrix is given by `rangeChartHom_coe`, which holds by `rfl`.
* `rangeChartHom_bijective ε he s`: this homomorphism is bijective.
* `rangeChartEquiv ε he s` is the resulting group isomorphism.
* `normOneChartPoints ε he s :
  (V ⟶ (normOneGroup τ).X) ≃* Matrix.symplecticGroup I R_V`. It composes the
  point equivalence of the represented subgroup `normOneAmbientι τ`
  (`isRepresentedBy_normOneAmbientι` with `IsRepresentedBy.pointsEquiv`)
  with `rangeChartEquiv`.
* `normOneChartPoints_val ε he s x` (by `rfl`): the underlying matrix of
  `normOneChartPoints ε he s x` is
  `chartAlong ε (pointScalars s) _` applied to the ambient tensor unit
  `FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) V (x ≫ (normOneAmbientι τ).hom.hom)`.
* `normOneChartPoints_naturality ε he t s x`: for `t : W ⟶ V`,
  `normOneChartPoints ε he (t ≫ s) (t ≫ x)` is
  `SymplecticMatrix.map I t.left.appTop.hom (normOneChartPoints ε he s x)`.
  So the chart points change by `t^*` on matrix entries.

There are no hypotheses on the characteristic or on the test scheme.

## Proof

*Base change of the compatibility.* `chartAlong_baseChange_mul_J` is proved
by induction on tensors. On a pure tensor `r ⊗ a`, `τ_R (r ⊗ a) = r ⊗ τ a`
and `χ (r ⊗ a) = r • (ε (1 ⊗ a)).map f` (`chartAlong_tmul`). Apply `he` to
`1 ⊗ a` and map the entries by `f`. Mathlib's `Matrix.map_mul`,
`Matrix.map_J` and `Matrix.transpose_map` then give
`(ε (1 ⊗ τ a)).map f * J_R = J_R * ((ε (1 ⊗ a)).map f)ᵀ`, and the scalar `r`
factors out of both sides. The additive case is linearity. Multiplying on
the right by `J_R` and using `J_R * J_R = -1` (`Matrix.J_squared`) gives
`chartAlong_baseChange`.

*Isometries.* By `chartAlong_baseChange`,
`χ (x * τ_R x) = -(M * J_R * Mᵀ * J_R)` for `M = χ x`. If `x * τ_R x = 1`,
then `-(M J Mᵀ J) = 1`. Multiplying on the right by `J_R` and negating
gives `M J Mᵀ = J`. Conversely, if `M J Mᵀ = J`, then
`-(M J Mᵀ J) = -(J J) = 1`, and `x * τ_R x = 1` because `χ` is injective
(`chartAlong_bijective`).

*The range equivalence.* `rangeChartHom` is well defined because
`mem_range_normOneAmbientι_iff` and `mem_range_isometryι_iff` show that
the tensor unit `u` of a range point satisfies `u * τ_R u = 1`. Its chart
image is then symplectic by `mul_baseChange_eq_one_iff`. Multiplicativity
follows from that of `FiniteAlgebraUnits.pointsEquiv` and of `χ`.
Injectivity follows from injectivity of `χ`, `Units.ext` and injectivity
of `FiniteAlgebraUnits.pointsEquiv`.

For surjectivity, let `g` be a symplectic matrix. Let `u` be the image of
the unit `SymplecticMatrix.toGL g` under the inverse of the bijective
algebra map `χ`, and let `y` be the ambient point with tensor unit `u`.

1. `u * τ_R u = 1`, by `mul_baseChange_eq_one_iff`, since `χ u = g` is
   symplectic.
2. The reduced norm of `y` is one. Apply the injective map `Gm.pointsEquiv`
   and `CentralSimpleUnits.reducedNormHom_points`. The reduced norm of `u`
   is `det (χ u) = det g` (`reducedNorm_eq_det_chartAlong`), and
   `det g = 1` by Mathlib's `SymplecticGroup.det_eq_one`. That lemma holds
   for symplectic matrices over every commutative ring, in every
   characteristic.

By `mem_range_normOneAmbientι_iff`, `y` therefore lies in the range, and
its image is `g`.

*Values and naturality.* `normOneChartPoints_val` holds by unfolding the
definitions. For naturality, the ambient point of `t ≫ x` is `t ≫` the
ambient point of `x` (`Category.assoc`). Its tensor unit is the base change
of that of `x` along `t^*` (`FiniteAlgebraUnits.pointsEquiv_naturality`).
Then `SpecialLinearInnerForm.chartAlong_naturality`, applied with
`pointScalars_comp` and `chartAlong_congr`, gives the entrywise image under
`t^*`.

## Provenance

The module states no result from external literature. It is derived
internal infrastructure: the algebraic content is the elementary fact that,
under a chart carrying `τ` to `M ↦ J Mᵀ J⁻¹`, the equation `u τ(u) = 1`
becomes `M J Mᵀ = J`. Together with Mathlib's theorem that symplectic
matrices have determinant one, this identifies the reduced-norm-one
involution isometries with `Sp(J)` on every test. The construction follows
the published special-linear chart module `SpecialLinearInnerForm.NormOneChart`.
