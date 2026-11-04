# Equivariant normal adjoint retractions from commuting normal complements

Worker 1522.

This module proves

```
normalAdjointEquivariantRetraction_of_semisimpleNormalComplement :
  SemisimpleNormalComplementStatement.{u} →
    NormalAdjointEquivariantRetractionStatement.{u}
```

It reduces the published target `NormalAdjointEquivariantRetractionStatement`
(`Adjoint/NormalEquivariantRetractionStatement.lean`) to
`SemisimpleNormalComplementStatement`
(`Reductive/SemisimpleNormalComplementStatement.lean`). That statement is a
hypothesis here and is not proved. It supplies a commuting closed normal
complement with flat surjective multiplication, the normal-subgroup part of
Milne, *Algebraic Groups* (2017), Theorem 21.51. Everything else in the target
is proved here. A trivial centre turns the almost-direct product into a direct
product. The published Levi retraction API then supplies the retraction, and
its equivariance follows from a second centre argument.

The derived route follows the target's Markdown: in a direct product
`H × K` with `Z(H) = 1`, the projection onto `H` is preserved by
automorphisms preserving `H`. This module does not use the scheme-theoretic
centralizer. It shows directly that the action carries `K` into the kernel of
the projection.

## Auxiliary results

Both are stated for group schemes `G`, `H`, `K` over `Spec k`, for an
arbitrary field `k : Type u`, with homomorphisms `j : H ⟶ G` and `i : K ⟶ G`.

- `mono_subgroupMultiplication_of_center_eq_bot`: if `center H = ⊥`, the
  underlying morphisms `j.hom.hom` and `i.hom.hom` are monic, and the points
  `x ≫ j.hom.hom` and `y ≫ i.hom.hom` commute for all test points `x`, `y`,
  then `subgroupMultiplication j i` is a monomorphism in `Over (Spec k)`.

  *Proof.* Let `p, p' : T ⟶ H.X ⊗ K.X` have equal composites with the
  multiplication. Write `a, n` and `a', n'` for their coordinates. By
  `comp_subgroupMultiplication`, `j(a) i(n) = j(a') i(n')` in the group of
  `T`-points of `G`. Hence `j(a'⁻¹ a) = i(n' n⁻¹)`, using
  `MonObj.mul_comp` and `GrpObj.inv_comp`. The point `c = a'⁻¹ a` is central
  in `H`. For `t : T' ⟶ T` and `h : T' ⟶ H.X`, apply `j` and cancel the
  monomorphism `j.hom.hom`. Then `j(t ≫ c) = i(t ≫ (n' n⁻¹))`, which commutes
  with `j(h)` by hypothesis. So `c = 1` by `center H = ⊥`, hence `a = a'`.
  Then `i(n' n⁻¹) = j(1) = 1`, so `n' n⁻¹ = 1` by cancelling `i.hom.hom`, hence
  `n = n'`. Finally `p = p'` by `CartesianMonoidalCategory.hom_ext`.

- `isIso_subgroupMultiplication_of_flat_of_surjective`: if `G.X` and `H.X`
  are affine over `Spec k`, `IsClosedSubgroup i` holds, and
  `subgroupMultiplication j i` is a monomorphism whose underlying scheme
  morphism is flat and surjective, then it is an isomorphism in
  `Over (Spec k)`.

  *Proof.* `G.X.left` and `H.X.left` are affine (`isAffine_of_isAffineHom`).
  `K.X.left` is affine because the closed immersion `i.hom.hom.left` is an
  affine morphism into an affine scheme. The source `(H.X ⊗ K.X).left` is the
  pullback of affine schemes over `Spec k`, hence affine. So the underlying
  morphism is quasi-compact, by Mathlib's instance for compact sources and
  quasi-separated targets. It is monic by `Over.mono_left_of_mono`. Mathlib's
  `Flat.isIso_of_surjective_of_mono` (`Morphisms/FlatMono.lean`) makes it an
  isomorphism of schemes, and the forgetful functor `Over.forget` reflects
  isomorphisms.

## Proof of `normalAdjointEquivariantRetraction_of_semisimpleNormalComplement`

Let `k` be algebraically closed, let `G` and `H` be adjoint, and let
`j : H ⟶ G` be a closed subgroup with normal range. Let `S` be a split torus,
and let `b`, `c` be automorphic actions of `S` on `G` and `H` with
`c.act s h ≫ j = b.act s (h ≫ j)` (the hypothesis `hbc`).

1. **Complement.** `IsAdjoint G` gives `IsSemisimple G`. `IsAdjoint H` gives
   smoothness and connectedness of `H` through `IsConnectedReductive`. The
   hypothesis then supplies `K`, a closed subgroup `i : K ⟶ G` with normal
   range, all-test commutation of `j` and `i`, and flatness and surjectivity of
   `(subgroupMultiplication j i).left`.
2. **Direct product.** Closed immersions are monic, so `j.hom.hom` and
   `i.hom.hom` are monic (`Over.mono_of_mono_left`). The first auxiliary
   result, with `center H = ⊥` from `IsAdjoint H`, makes the multiplication a
   monomorphism. The second, with affineness from `IsConnectedReductive`, makes
   it an isomorphism.
3. **Retraction.** Take `r = leviRetraction j i hiN`
   (`Rational/LeviRetraction.lean`), where `hiN` is normality of `range i`.
   Then `j ≫ r = 𝟙 H` is `levi_comp_leviRetraction`. On points,
   `g ≫ r.hom.hom = leviComponent j i g` (`comp_leviRetraction`).
4. **The action kills the complement coordinate.** For `s : T ⟶ S.X` and
   `n : T ⟶ K.X`, let `e = leviComponent j i (b.act s (n ≫ i.hom.hom))`. It
   lies in `center H`. For `t : T' ⟶ T` and `h : T' ⟶ H.X`, put `s' = t ≫ s`
   and `h' = c.act s'⁻¹ h`, so `c.act s' h' = h` by `act_mul_left`,
   `mul_inv_cancel` and `act_one_left`. By `leviComponent_comp` and
   `AutomorphicAction.naturality`,
   `t ≫ e = leviComponent j i (b.act s' ((t ≫ n) ≫ i.hom.hom))`. The points
   `(t ≫ n) ≫ i.hom.hom` and `h' ≫ j.hom.hom` commute. Map this commutation by
   the group automorphism `b.pointAut T' s'` and then by the group
   homomorphism `leviRetractionPoints j i hiN T'` (`Commute.map`). The second
   point becomes `leviComponent j i (c.act s' h' ≫ j.hom.hom) = h`, by `hbc`
   and `leviComponent_comp_levi`. Hence `t ≫ e` commutes with `h`. Since
   `center H = ⊥`, `e = 1`.
5. **Equivariance.** For `g : T ⟶ G.X`, write
   `g = (leviComponent j i g ≫ j.hom.hom) * (radicalComponent j i g ≫ i.hom.hom)`
   (`leviComponent_mul_radicalComponent`). The action is multiplicative
   (`act_mul_right`). The first factor becomes
   `c.act s (leviComponent j i g) ≫ j.hom.hom` by `hbc`. The Levi coordinate
   is multiplicative because `range i` is normal (`leviComponent_mul`). It
   returns `c.act s (leviComponent j i g)` on the first factor
   (`leviComponent_comp_levi`) and `1` on the second, by step 4. Hence
   `b.act s g ≫ r.hom.hom = c.act s (g ≫ r.hom.hom)`.

No fppf-local lifting of points is needed. Every identity is proved on the
original test scheme, for arbitrary schemes over `Spec k`, including
nonreduced ones. Only `center H = ⊥` is used from the adjointness of `H`,
together with its smoothness, connectedness and affineness. From `G`, the
proof uses semisimplicity (to apply the hypothesis) and affineness. Triviality
of the centre of `G` and the split-torus hypothesis on `S` are not used.
