# Canonical maps from base-changed adeles to adeles of an extension

Author: Worker 105.

For a finite extension `L/K` of global fields, this module defines the canonical `L`-algebra
map `L ⊗[K] A_K → A_L`, `a ⊗ x ↦ a · ι(x)`. Here `ι : A_K → A_L` views an adele of `K` as an
adele of `L`: its coordinate at a place `w` of `L` is the completed embedding `K_v → L_w` applied
to the coordinate at the place `v` of `K` below `w`. For function fields the module also
constructs `ι`; for number fields it is the published `AdelicFunctoriality.adeleInclusion`.

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Example 4.2 (printed pp.9–10) and Proposition 5.14 (printed p.20),
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Both results identify the
adelic points of a Weil restriction `Res_{L/K}(X')` with the adelic points of `X'`. The
identification is the point identification `Res_{L/K}(X')(A_K) = X'(L ⊗[K] A_K)` followed by
change of coefficients along this map. The module defines the map and its formulas only. That
it is an isomorphism (the tensor decomposition of the adeles) is not claimed here.

## Function fields

The fields `k`, `K` and `L` lie in one universe, with algebra structures `k → K`, `k → L`,
`K → L`, the scalar tower `k → K → L`, and `FiniteDimensional K L`. No separability or
perfectness is assumed for these constructions.

- `curvePlaceCompletionMap_mem_integers`: for a place `p` of `K` and an upper place `q` above
  `p` (`CurvePlacesAbove k L p`), the published completed embedding
  `CurvePlaceCompletionExtension.completionMap p q` maps completed integers to completed
  integers. The set of points mapping into the closed valuation subring at `q` is closed.
  It contains the images of the integral elements of `K`, since the original embedding maps
  the valuation ring of `p` into that of `q` (`CurvePlaceCompletionExtension.mem_iff`).
  Those images are dense in the open valuation subring at `p`.
- `curvePlaceAboveRestriction q`: an upper place `q` lies above its restriction
  `curvePlaceRestriction q` (published in `Langlands/Global/ArithmeticExceptionalSets.lean`).
- `curvePlaceAdeleInclusion k K L : CurvePlaceAdeleRing k K →+* CurvePlaceAdeleRing k L` is
  Mathlib's `RestrictedProduct.mapAlongRingHom` along restriction of places, which has finite
  fibres (published `curvePlaceRestriction_tendsto_cofinite`), with coordinate maps the
  completed embeddings. `curvePlaceAdeleInclusion_apply` is the coordinate formula, and
  `continuous_curvePlaceAdeleInclusion` is its continuity (Mathlib's
  `RestrictedProduct.mapAlong_continuous`).

The remaining function-field constructions also assume a perfect constant field and that `K`
and `L` are function fields over `k` (`FunctionField k K`, `FunctionField k L`, with
`RatFunc k`-algebra structures and scalar towers). These are the hypotheses of the published
diagonal `curvePlaceAdeleDiagonal`, which gives the algebra structures of the adele rings over
the fields. The two `RatFunc k`-structures are independent: the diagonal maps do not depend
on them.

- `curvePlaceAdeleInclusion_diagonal`: `ι` maps the principal adele of `x ∈ K` to the principal
  adele of its image in `L`, by the published `completionMap_algebraMap`.
- `curvePlaceAdeleTensorMap k K L : L ⊗[K] CurvePlaceAdeleRing k K →ₐ[L] CurvePlaceAdeleRing k L`
  is `Algebra.TensorProduct.lift` of the structure map of `L` and of `ι`, which is a
  `K`-algebra map by the diagonal formula. `L` acts on the tensor product through the left
  factor.
- `curvePlaceAdeleTensorMap_tmul`: `a ⊗ x ↦ a · ι(x)`. The generator identities are
  `curvePlaceAdeleTensorMap_tmul_one` (`a ⊗ 1 ↦` the principal adele of `a`) and
  `curvePlaceAdeleTensorMap_one_tmul` (`1 ⊗ x ↦ ι(x)`).
  `curvePlaceAdeleTensorMap_tmul_apply` is the coordinate formula at an upper place `q`: the
  image of `a` in the completion at `q` times the completed embedding of the coordinate of
  `x` at the restriction of `q`.

## Number fields

`K` and `L` are number fields with an algebra structure `K → L`; Mathlib's adele rings
`Adeles K` and `Adeles L` include every infinite place.

- `numberFieldAdeleTensorMap K L : L ⊗[K] Adeles K →ₐ[L] Adeles L` is `Algebra.TensorProduct.lift`
  of the structure map of `L` and of the published `AdelicFunctoriality.adeleInclusion`. The
  latter is a `K`-algebra map by the published `adeleInclusion_diagonal`.
- `numberFieldAdeleTensorMap_tmul`, `numberFieldAdeleTensorMap_tmul_one` and
  `numberFieldAdeleTensorMap_one_tmul` are the same formulas as for function fields.
- `numberFieldAdeleTensorMap_tmul_infinite` and `numberFieldAdeleTensorMap_tmul_finite` are the
  coordinate formulas at an infinite place `w` of `L` (through `infiniteCompletionMap` at the
  place below `w`) and at a finite place `q` of `L` (through `FiniteExtension.completionMap` at
  `q.under`).

## Derived content

The names, the packaging through `Algebra.TensorProduct.lift`, the use of the left `L`-algebra
structure on the tensor product, and the function-field inclusion `ι` are derived. The
inclusion is the function-field analogue of the published number-field `adeleInclusion`.
