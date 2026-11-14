# Assembling the degree-two comparison for abelian varieties

Module `Langlands.AbelianScheme.DegreeTwoComparisonAssembly`, namespace `Langlands.AbelianScheme`.

## Purpose

This module joins the published pieces about structure-sheaf cohomology of an abelian scheme
`A` over a field `K`:

- primitivity and the multiplication formula `pullStructure_mul_cupA` (`CanonicalH1Primitive`),
- the dimension count (`StructureCohomologyKunnethDimension`),
- cover independence of the cup product (`CechResolution.AllSeqRefine`),
- the linear-algebra reduction `BoundedExteriorSquareCoproduct.exists_comparison`.

It reduces `FieldH2ExteriorCoproductComparisonStatement` to three inputs, stated as hypotheses
and not proved here: injectivity of the explicit comparison map `degreeTwoMap A`, alternation of
the cup product `cupA A`, and a bounded creation-contraction family on `H*(A, 𝒪)`.

Notation: `Hⁿ(X) = structureCohomology X n = (relativeCohomology X.hom n).obj 𝒪_X`;
`P = A.X ⨯ A.X`; `p₁ = prod.fst`, `p₂ = prod.snd`, `m = p₁ * p₂`; `f^* = pullStructure A f n`,
the canonical pullback followed by `pullbackUnitIso`, as in the target statement.

## Second tensor power (section `TensorTwo`)

For any commutative ring `K` and `K`-module `H`:

- `tensorPowerTwoEquiv K H : ⨂[K]^2 H ≃ₗ[K] H ⊗[K] H` is the inverse of Mathlib's
  `TensorPower.mulEquiv` in degrees `1 + 1`, followed by `PiTensorProduct.subsingletonEquiv` on both
  factors.
- `tensorPowerTwoEquiv_tprod`: `tprod K v ↦ v 0 ⊗ v 1`.
- `tensorPowerTwoEquiv_toTensorPower_ιMulti`: the antisymmetrization
  `exteriorPower.toTensorPower K H 2 (ιMulti K 2 v)` maps to `v 0 ⊗ v 1 - v 1 ⊗ v 0`.

## Binary-tensor dimension count and covers (section `Abelian`)

- `bijective_of_injective_degreeTwo_tensor A Φ hΦ`: every injective `K`-linear map
  `Φ : H²(A) × (H¹(A) ⊗[K] H¹(A)) × H²(A) ⟶ H²(P)` is bijective. Both sides have dimension
  `dim H²(A) + (dim H¹(A))² + dim H²(A)` (`finrank_structureCohomology_prod_two` and
  `Module.finrank_tensorProduct`).
- `degreeTwoTensorEquivOfInjective A Φ hΦ` is the corresponding linear equivalence, with
  `degreeTwoTensorEquivOfInjective_apply`.
- `mixedCover A` is the cover `FieldTwoAxisH1Injectivity.prodCover p₁ p₂ (cover A) (cover A)`
  of `P` by the opens `p₁⁻¹ U a ⊓ p₂⁻¹ U b`. The lemmas are `mixedCover_top`,
  `mixedCover_affine` and `productCover_le_mixedCover`; the last says that `productCover A` refines
  `mixedCover A` along `Prod.fst`.
- `cupP_eq_mixedCover`: `cupP A x y` equals `AllSeq.cupCanonical` computed on `mixedCover A`.
  This is `AllSeq.cupCanonical_refine`. A mixed cup defined on `mixedCover A` therefore agrees
  with the one defined through `cupP`.
- `mixedTensorA A : H¹(A) ⊗[K] H¹(A) ⟶ H²(P)` is the lift of `x ⊗ y ↦ cupP A (p₁^* x) (p₂^* y)`.
  The lemmas are `mixedTensorA_tmul`, and `mixedTensorA_tmul_eq_mixedCover`, which gives the same
  value with the cup computed on `mixedCover A`.
- `degreeTwoMap A (a, t, b) = p₁^* a + (mixedTensorA A t + p₂^* b)`, with `degreeTwoMap_apply`.

## Conditional assembly (section `Assembly`)

- `cupAlt A halt` is the alternating map `v ↦ cupA A (v 0) (v 1)` on `Fin 2`. It requires
  `halt : ∀ x, cupA A x x = 0`.
- `exists_comparison_of_inputs`: assume

  1. `hinj : Function.Injective (degreeTwoMap A)`,
  2. `halt : ∀ x, cupA A x x = 0`,
  3. a finite index type `I`, linear maps
     `c i n : Hⁿ(A) ⟶ Hⁿ⁺¹(A)` and `d i n : Hⁿ⁺¹(A) ⟶ Hⁿ(A)` satisfying
     `d i (n+1) ∘ c j (n+1) + c j n ∘ d i n = if i = j then id else 0`,
     `Hⁿ(A) = 0` (as `Subsingleton`) for `n > card I`, and vectors `v : I → H¹(A)` with
     `c i 1 x = cupA A (v i) x`.

  Then there are `e : H²(A) ≃ₗ[K] ⋀[K]^2 H¹(A)` and
  `κ : H²(P) ≃ₗ[K] H²(A) × ⨂[K]^2 H¹(A) × H²(A)` with
  `κ (p₁^* x) = (x, 0, 0)`, `κ (p₂^* x) = (0, 0, x)` and
  `κ (m^* x) = (x, toTensorPower (e x), x)`.

  Proof: `κ` is the inverse of `degreeTwoTensorEquivOfInjective A (degreeTwoMap A) hinj`, followed
  by `tensorPowerTwoEquiv⁻¹` on the middle factor. The formulas for `p₁^*` and `p₂^*` hold by
  construction. For `m^*` on a cup `cupA A (w 0) (w 1)`, `pullStructure_mul_cupA` gives
  `p₁^*(w₀ ∪ w₁) + p₁^*w₀ ∪ p₂^*w₁ - p₁^*w₁ ∪ p₂^*w₀ + p₂^*(w₀ ∪ w₁)`. This equals
  `degreeTwoMap A (cup w, w₀ ⊗ w₁ - w₁ ⊗ w₀, cup w)`, and
  `tensorPowerTwoEquiv_toTensorPower_ιMulti` identifies the middle entry. Then
  `BoundedExteriorSquareCoproduct.exists_comparison` with `cup = cupAlt A halt` extends the
  formulas from cup generators to all of `H²(A)` and produces `e`.
- `fieldH2ExteriorCoproductComparison_of_inputs`: if the inputs of `exists_comparison_of_inputs`
  hold for every abelian scheme over every field (in universe `u`), then
  `FieldH2ExteriorCoproductComparisonStatement.{u}` holds. Its conclusion is the target's
  statement verbatim.

## Scope

Injectivity of `degreeTwoMap A`, alternation of `cupA A` and the creation-contraction family are
hypotheses here; none of them is proved in this module. The excluded Picard and dual-scheme
statements and any proof of `FieldH2PrimitiveInjectivityStatement` are not imported; the target
statement module is imported unchanged.

## Provenance

This is an internal derivation, combining finite-dimensional linear algebra (Mathlib tensor
powers, `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`) with published Library
results. The three-summand decomposition of `H²(A ⨯ A, 𝒪)` and the coproduct formula
`m^*(x ∪ y) = p₁^*(x ∪ y) + p₁^*x ∪ p₂^*y - p₁^*y ∪ p₂^*x + p₂^*(x ∪ y)` are the degree-two case of
the bialgebra structure on `H*(A, 𝒪)` (Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft, (6.12)–(6.17)). This module only assembles them.
