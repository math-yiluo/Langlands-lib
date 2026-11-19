# Weil truncation quotients through the transitivity index

`Langlands.Ramification.Kummer.truncationWeilQuotient` proves
`TruncationWeilQuotientStatement.{u}`. Let `F` be a p-adic field, `E` a finite
intermediate extension with Weil group `W_E` (over `E.asPadicField`), and `μ` a
real number with `E.field.fixingSubgroup ⊔ G_F^μ = ⊤`. For every `x` with
`-1 ≤ x ≤ μ`, `WeilTruncationIsoAt F E x` holds: there is a continuous
multiplicative equivalence `φ : W_E/R_E(x) ≃ₜ* W_F/R_F(x)` with
`φ (mk w) = mk (intermediateWeilMap F E w)` that carries the image of `R_E(y)`
onto the image of `R_F(y)` for every `-1 ≤ y ≤ x`. Here `R_F(x)` is
`upperGroup F x`, the preimage of `G_F^x` under `localProjection F`. As in the
statement module, a local instance supplies the normality of `R_F(x)` used by
the quotient groups.

The module proves the following auxiliary results and then the target. Write
`ι = intermediateWeilMap F E`.

## Upper groups above `-1` lie in inertia

- `upperRamificationGroup_le_zero_of_neg_one_lt`: in a finite Galois
  extension, the upper group at `x > -1` is contained in the upper group at
  `0`. Both are the integer-indexed lower groups at `⌈ψ(x)⌉` and at
  `⌈ψ(0)⌉ = 0` (`upperRamificationGroup_eq_lower`, `herbrandPsi_zero`).
  Since `ψ` is strictly increasing with `ψ(-1) = -1`, `ψ(x) > -1`, so
  `⌈ψ(x)⌉ ≥ 0`, and the lower filtration is antitone.
- `absoluteUpperRamificationGroup_le_inertia_of_neg_one_lt`: for `x > -1`,
  `G_F^x` is contained in the absolute inertia group
  `F.absoluteInertia F.canonicalTopologicalData`. This applies the previous
  lemma at every finite Galois level (`mem_absoluteUpperRamificationGroup_iff`)
  and identifies `G_F^0` with absolute inertia by
  `HerbrandBridge.absoluteUpperCanonicalInertia`.
- `exists_localProjection_eq_of_mem_inertia`: an element `h` of absolute
  inertia is the projection of a Weil element, namely the pair `(h, 1)` of the
  Weil pullback; it lies in the pullback because `h` is in the kernel of
  `localResidueDegree F` (`localResidueDegree_ker`).

## Every Weil element splits along `ι(W_E)` and `R_F(x)`

`exists_upperGroup_mul_mem_range`: under the transitivity hypothesis, for
`-1 ≤ x ≤ μ` and every `w ∈ W_F` there is `i ∈ R_F(x)` with
`w i⁻¹ ∈ ι(W_E)`.

- If `x = -1`, `R_F(-1) = W_F` (`absoluteUpperRamificationGroup_neg_one`),
  and `i = w` works.
- If `x > -1`, the projection of `w` lies in
  `E.field.fixingSubgroup ⊔ G_F^μ = ⊤`; since `G_F^μ` is normal,
  `Subgroup.mem_sup_of_normal_right` writes it as `g h` with
  `g ∈ E.field.fixingSubgroup` and `h ∈ G_F^μ`. As `μ ≥ x > -1`, `h` lies in
  inertia, so `h` is the projection of some `i ∈ W_F`. Then `i ∈ R_F(x)` by
  antitonicity of the absolute filtration, and `w i⁻¹` projects to `g`, so it
  lies in `pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)`,
  which is the range of `ι` (`intermediateWeilMap_range`).

## `ι` is an open map

`intermediateWeilMap_isOpenMap`: `ι` is an embedding
(`intermediateWeilMap_isEmbedding`) whose range, the pullback fixing
subgroup, is open (`pullbackFixingSubgroup_open`); hence it is an open
embedding and an open map.

## The quotient isomorphism

`weilQuotientIsoAlong_of_comap` works for arbitrary `K F : PadicField.{u} p`
and any continuous homomorphism `ι : W_K →ₜ* W_F`. It assumes `-1 ≤ x`, that
the preimage of `R_F(y)` under `ι` is `R_K(y)` for every `-1 ≤ y ≤ x`, the
splitting property above, and that `ι` is an open map; it concludes
`WeilQuotientIsoAlong K F ι x`.

- The map `f = QuotientGroup.map` of `ι` is well defined because
  `R_K(x) ≤ ι⁻¹(R_F(x))`. It is injective because `ι(w) ∈ R_F(x)` forces
  `w ∈ R_K(x)`, and surjective because for `w ∈ W_F` with `w i⁻¹ = ι(a)` one
  has `ι(a)⁻¹ w = i ∈ R_F(x)`. This gives a multiplicative equivalence `e`
  with `e (mk w) = mk (ι w)`.
- `e` is continuous because `mk` is a quotient map and `mk ∘ ι` is continuous.
  `e` is an open map: the image of a set `s` equals `mk (ι (mk⁻¹ s))`; the
  preimage is open, `ι` is an open map, and `QuotientGroup.isOpenMap_coe`.
  `Equiv.toHomeomorphOfContinuousOpen` then gives the continuous inverse, and
  `e` with these two continuity proofs is the required `φ`. This route does
  not use compactness: `W_E` is not compact.
- Filtration: by `Set.image_image` the image of `mk(R_K(y))` under `φ` is
  `mk(ι(R_K(y)))`. Every `ι(a)` with `a ∈ R_K(y)` lies in `R_F(y)` by the
  preimage hypothesis at `y`. Conversely, for `r ∈ R_F(y)` the splitting gives
  `i ∈ R_F(x) ⊆ R_F(y)` (`upperGroup_antitone`) and `a` with `ι(a) = r i⁻¹`.
  Then `ι(a) ∈ R_F(y)`, so `a ∈ R_K(y)`, and `mk(ι(a)) = mk(r)` because
  `ι(a)⁻¹ r = i ∈ R_F(x)`.

## The target

`truncationWeilQuotient` applies `weilQuotientIsoAlong_of_comap` with
`K = E.asPadicField` and `ι = intermediateWeilMap F E`. It uses
`truncationWeilComap` (Task 7663) at each `y` with `-1 ≤ y ≤ x ≤ μ` for the
preimage hypothesis, `exists_upperGroup_mul_mem_range` for the splitting,
and `intermediateWeilMap_isOpenMap` for openness. The general lemma is stated
over arbitrary `K` because instance resolution does not find the local
normality instance when `E.asPadicField` appears literally.

This is Lemma `lem:trunc` of the operator route note
`operator-numerical-llc-route-2026-11-16` (lines 876–889), in the Weil-group
form. The [statement's documentation](TruncationQuotientStatement.md)
explains the formulation.
