# Finitely many separating sections, assuming the local criterion

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.FiniteSeparatingSectionsStatement`. It is internal: it is not a
Library statement. Its main theorem is conditional:

- `Langlands.AlgebraicGeometry.finiteSeparatingSections_of
  (hLoc : ProperRationalImmersionLocalClosedImmersionStatement) :
  FiniteSeparatingSectionsStatement`, for every universe `u`.

So `FiniteSeparatingSectionsStatement` follows from the local closed-immersion criterion
`ProperRationalImmersionLocalClosedImmersionStatement`. This module imports the published
proof `linearSystemMorphism` of `LinearSystemMorphismStatement` from
`LinearSystemMorphismProof`; only the local criterion remains a premise.

Provenance. Milne applies the very-ampleness criterion to the complete linear system `|3D|`
(proof of Theorem 7.1, pp.10–11 of `milne-abelian-varieties-1986-author-2022`). That linear
system is finite-dimensional because `Γ(X, L)` is finite-dimensional for proper `X`. Here
finite-dimensionality is not available. Instead, a finite set of sections whose span
separates points and tangent vectors is found by Noetherian induction, and openness of
separation comes from the local criterion. This route is our own. The other lemmas are in the
namespace `Langlands.AlgebraicGeometry.FiniteSeparating`.

Throughout, `K` is an algebraically closed field, `p : X ⟶ Spec K` and `L` is a line bundle
on `X`. "Rational point" means Library's `IsRationalPoint p x` (`x ≫ p = 𝟙`), and the point
of `X` underlying `x` is the image of the closed point of `Spec K`. The span of a finite set
`S` of sections, `enum S` and `SeparatesAt p L S x` are from the helper module
`FiniteSeparating.Span`. `sectionRatio`, `vanishesAlong_iff_not_mem` and
`vanishesAlong_iff_sectionRatio_eq_zero` are from `LinearSystem.SectionRatio`, and
`forall_mem_of_mem`, `forall_mem_of_augmentation_comp` are from `LinearSystem.DualNumberPoints`.
By `vanishesAlong_iff_not_mem`, a section `σ` vanishes at a rational point exactly when the
point lies outside `trivializationOpen L.obj σ`.

## General lemmas

- `eq_top_of_forall_rationalPoint_mem`: if `p` is locally of finite type, an open `U`
  containing every rational point is all of `X`. `X` is a Jacobson space
  (`LocallyOfFiniteType.jacobsonSpace`). If `U ≠ ⊤`, its closed complement contains a closed
  point `c` (`nonempty_inter_closedPoints`). Since `K` is algebraically closed, `c` comes from
  a rational point (`pointOfClosedPoint`, `pointOfClosedPoint_comp`,
  `pointOfClosedPoint_apply`). That rational point lies in `U`, which is a contradiction.
- `eq_of_comp_eq_of_mono`: let `f : X ⟶ Y` and `V` an open of `Y` such that `f ∣_ V` is a
  monomorphism. If `g₁ ≫ f = g₂ ≫ f` and `g₁` maps into `f⁻¹ V`, then `g₁ = g₂`. Both maps
  land in `f⁻¹ V`, so both factor through the open immersion `(f⁻¹ V).ι`
  (`IsOpenImmersion.lift`). The two lifts agree after the monomorphism `f ∣_ V ≫ V.ι`
  (`morphismRestrict_ι`), so they are equal.

## Step 1: a finite set without common zeros

`exists_finset_forall_mem`: if `p` is proper and `L` separates points and tangent vectors
(Library's `SeparatesPointsAndTangents p L`), there is a finite set `S₀` of sections such that
every point of `X` lies in `trivializationOpen L.obj σ` for some `σ ∈ S₀`. The first clause
of `SeparatesPointsAndTangents` gives, for each rational point, a section not vanishing there.
So the union of all the opens `trivializationOpen L.obj σ` contains every rational point, and
it is `⊤` by `eq_top_of_forall_rationalPoint_mem`. `X` is quasi-compact
(`QuasiCompact.compactSpace_of_compactSpace`), so finitely many of these opens cover it.

## Step 2: separating one rational point from the other rational points

`awayOpen p L S x` is the union of `trivializationOpen L.obj σ` over the sections `σ` in the
span of `S` that vanish at `x` (`mem_awayOpen_iff`). It grows with `S` (`awayOpen_mono`). A
rational point `y` lies in it exactly when some `σ` in the span of `S` vanishes at `x` but not
at `y`.

`exists_separates_points`: for a rational point `x` and a finite set `S₀`, there is a finite
`S ⊇ S₀` whose span separates `x` from every other rational point. `X` is locally Noetherian
(`LocallyOfFiniteType.isLocallyNoetherian`) and quasi-compact, hence a Noetherian space. Its
opens satisfy the ascending chain condition (`wellFounded_gt`), so there is `S ⊇ S₀` for
which `awayOpen p L S x` is maximal. If a rational point `y ≠ x` is not in `awayOpen p L S x`,
take `σ₁` vanishing at `x` and not at `y` (second clause of `SeparatesPointsAndTangents`).
Then `awayOpen p L (insert σ₁ S) x` contains `y`, so it is strictly larger. This contradicts
maximality.

## Step 3: separating a rational point from its tangent vectors

`exists_separates_tangents`: for a rational point `x` and a finite set `S₁`, there is a finite
`S ⊇ S₁` such that for every nonzero tangent vector `t` at `x`, some section in the span of
`S` vanishes at `x` but not along `t`.

Choose `s₀` not vanishing at `x`, and an affine open `U` containing the point of `x` with
`U ⊆ trivializationOpen L.obj s₀` (`exists_isAffineOpen_mem_and_subset`). The ring
`Γ(U, ⊤)` is Noetherian (`IsLocallyNoetherian.component_noetherian`). `ratioIdeal p L U s₀ S x`
is the ideal of `Γ(U, ⊤)` generated by the ratios `sectionRatio L U.ι σ s₀` of the sections
`σ` in the span of `S` that vanish at `x`. Choose `S ⊇ S₁` for which this ideal is maximal
(`set_has_maximal_iff_noetherian`).

Let `t` be a nonzero tangent vector at `x`. Take `σ₁` vanishing at `x` and not along `t`
(third clause of `SeparatesPointsAndTangents`). Suppose no section in the span of `S` vanishes
at `x` but not along `t`. The map `t` lands in `U` (`forall_mem_of_augmentation_comp`), so
`t = t' ≫ U.ι` with `t' = IsOpenImmersion.lift U.ι t _`. A section `σ` vanishes along `t`
exactly when `t'^#(sectionRatio L U.ι σ s₀) = 0` (`vanishesAlong_iff_sectionRatio_eq_zero`,
`sectionRatio_comp`). Hence `ratioIdeal p L U s₀ S x` lies in the kernel of `t'^#`. By
maximality, adding `σ₁` to `S` does not change the ideal, so the ratio of `σ₁` is in the
kernel. Then `σ₁` vanishes along `t`, a contradiction.

## Step 4: separation is open

`exists_open_separatesAt (hLoc)`: let `p` be proper, `S` a finite set of sections without
common zeros, and `x` a rational point with `SeparatesAt p L S x`. Then there is an open `W`
containing the point of `x` such that `SeparatesAt p L S x'` holds for every rational point
`x'` in `W`.

Apply the published `linearSystemMorphism` to `enum S`, which has no common zeros
(`exists_enum_eq`, Library's
`lineBundleResidueOpenComparison`). This gives `φ : X ⟶ ProjectiveSpace K S.card` over
`Spec K` with the two vanishing dictionaries of `LinearSystemMorphismStatement`. The map `φ`
is proper: `φ ≫ projectiveSpaceToSpec K S.card = p` is proper, and
`projectiveSpaceToSpec K S.card` is proper, hence separated (Library instance
`projectiveSpaceToSpec_isProper`), so `IsProper.of_comp` applies. The same instance supplies
the hypothesis of `hLoc` that projective space is locally of finite type over `Spec K`. Next check the hypotheses of `hLoc` at `x`.

- If `y ≫ φ = x ≫ φ` for a rational point `y ≠ x`, then `SeparatesAt` gives a combination of
  `enum S` vanishing at `x` but not at `y` (`inSpan_iff`). This contradicts the rational-point
  dictionary supplied by `linearSystemMorphism`.
- If `t ≫ φ = (dualNumberProjection K ≫ x) ≫ φ` for a tangent vector `t` at `x` different
  from `dualNumberProjection K ≫ x`, then `t` is a nonzero tangent vector. `SeparatesAt` gives
  a combination vanishing at `x` but not along `t`, which contradicts the tangent-vector
  dictionary supplied by `linearSystemMorphism`.

So `hLoc` gives an open `V` of projective space containing the image of `x` such that
`φ ∣_ V` is a closed immersion, hence a monomorphism. Take `W = φ⁻¹ V`. Let `x'` be a rational
point in `W`.

- Let `y ≠ x'` be a rational point. If every combination vanishing at `x'` also vanished at
  `y`, the rational-point dictionary would give `x' ≫ φ = y ≫ φ`. Then `x' = y` by
  `eq_of_comp_eq_of_mono`, since `x'` maps into `W` (`forall_mem_of_mem`).
- Let `t` be a nonzero tangent vector at `x'`. If every combination vanishing at `x'` also
  vanished along `t`, the tangent-vector dictionary would give
  `t ≫ φ = (dualNumberProjection K ≫ x') ≫ φ`.
  Since `t` maps into `W` (`forall_mem_of_augmentation_comp`), `eq_of_comp_eq_of_mono` gives
  `t = dualNumberProjection K ≫ x'`. This contradicts the assumption that `t` is nonzero.

## Step 5: the finite family

`finiteSeparatingSections_of hLoc`: let `X` be proper over `K` and `L` separate points and
tangent vectors. Take `S₀` from Step 1. For each rational point `x`, Steps 2 and 3 give finite
sets `S₀ ⊆ S₁ ⊆ S_x` with `SeparatesAt p L S_x x`. Step 4 gives an open `W_x` containing the
point of `x` on whose rational points `S_x` separates. The union of the `W_x` contains every
rational point, so it is `⊤` (`eq_top_of_forall_rationalPoint_mem`). By quasi-compactness,
finitely many `W_x`, for `x` in a finite set `F`, cover `X`. Let `S = S₀ ∪ ⋃_{x ∈ F} S_x`.
Every rational point `x'` lies in some `W_x` with `x ∈ F`, so `SeparatesAt p L S_x x'`, and
`SeparatesAt p L S x'` by `SeparatesAt.mono`.

The statement holds with `n = S.card` and `s = enum S`:

1. every point lies in `nonvanishingLocus L.obj σ` for some `σ ∈ S₀ ⊆ S`
   (`lineBundleResidueOpenComparison` identifies it with `trivializationOpen L.obj σ`), and
   `σ` occurs in `enum S`;
2. and 3. the sections provided by `SeparatesAt p L S x` are combinations of `enum S` by
   `inSpan_iff`.
