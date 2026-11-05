# Factorizations of split tori through maximal and central split tori

Author: Worker 228.

This module derives three factorization results from the split-torus image theorem of
[`SplitTorusImage`](SplitTorusImage.md). It also supplies the product homomorphism of two
homomorphisms with commuting values. All declarations are in `Langlands.GroupScheme`.

## Product homomorphisms

Over an arbitrary base scheme `S`, let `a : A ⟶ M` and `b : B ⟶ M` be homomorphisms of group
schemes. Let `hab` say that their values commute over every test scheme.

* `prodPoints a b hab T` sends a point `p` of `A ⊗ B` (the categorical product, with points
  `productPointsEquiv`) to `a(p₁) * b(p₂)`. It is multiplicative by
  `Commute.mul_mul_mul_comm`, and natural by `productPointsEquiv_naturality`.
* `prodHom a b hab : A ⊗ B ⟶ M` is the homomorphism given by the published `homOfPoints`, with
  `comp_prodHom` as its point formula.
* `prodInl A B : A ⟶ A ⊗ B` and `prodInr A B : B ⟶ A ⊗ B` are the inclusions `x ↦ (x, 1)` and
  `y ↦ (1, y)`, built from the point homomorphisms `inlPoints` and `inrPoints`.
  `prodInl_prodHom` and `prodInr_prodHom` say that they recover `a` and `b`.
* `isCentral_prodHom`: the product of two central homomorphisms is central, since the centre
  is a subgroup functor.
* `IsCentral.commute_values`: the values of a central homomorphism commute with the values of
  any homomorphism, by `commute_of_mem_center`.

## Factorizations over a field

Let `k` be a field, with `𝕊 = Spec k`.

`IsMaximalSplitTorus.exists_factor_of_commute` works over any field. In an affine
group scheme `M`, every homomorphism from a split torus whose values commute on
all test schemes with those of a supplied maximal split torus factors through
that maximal split torus. The proof forms their product homomorphism and uses
`IsSplitTorus.exists_factor_isSplitSubtorus'` to construct its closed split image.
Maximality makes the second factor's map to that image an isomorphism. Composing
the first factor with its inverse gives the required factorization. No
reductivity or smoothness premise is used.

This general commuting factorization was contributed by Worker 1562 and is
shared by the derived split-torus and central-cover normalizer constructions.

* `IsSplitTorus.exists_factor_isSplitSubtorus'` is the image theorem for a split torus `D` given
  only as a group scheme. It applies `IsSplitTorus.exists_factor_isSplitSubtorus` to the
  commutative group scheme `splitTorus.commGroupScheme 𝕊 I` and the composite `e⁻¹ ≫ φ`, where
  `e : D ≅ splitTorus 𝕊 I`.

Let now `M` have affine structure morphism.

* `IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`: let `j : M ⟶ G` be a closed
  subgroup and `t : T ⟶ M` a homomorphism such that `t ≫ j` is a maximal split torus of `G`.
  Then every central split torus `a : A ⟶ M` factors as `g ≫ t = a`.
  *Proof.* The values of `a` commute with those of `t`, so `prodHom a t : A ⊗ T ⟶ M` is
  defined. `A ⊗ T` is a split torus (`IsSplitTorus.tensor`). The image theorem gives
  `π ≫ i' = prodHom a t` with `i'` a split subtorus. Then `i' ≫ j` is a split subtorus of `G`,
  and `(prodInr ≫ π) ≫ i' ≫ j = t ≫ j`. By maximality of `t ≫ j`, `prodInr ≫ π` is an
  isomorphism `e`. Finally `g := (prodInl ≫ π) ≫ e⁻¹` satisfies `g ≫ t = a`.
* `IsSplitComponent.exists_factor`: let `iA : A ⟶ M` be a split component of `M`, and
  `b : B ⟶ M` a central homomorphism from a split torus. Then `b` factors as `f ≫ iA = b`.
  *Proof.* As above, now with `prodHom b iA`. The product of two central homomorphisms is
  central, so by the centrality clause of the image theorem the image `i'` is a central split
  torus. Since `(prodInr ≫ π) ≫ i' = iA`, maximality of the split component makes
  `prodInr ≫ π` an isomorphism, and `f := (prodInl ≫ π) ≫ (prodInr ≫ π)⁻¹`.

## Provenance

These are internal consequences of the image theorem and of the published definitions
`IsSplitSubtorus`, `IsMaximalSplitTorus`, `IsCentralSplitTorus` and `IsSplitComponent`. They
make no further claim from the literature.
