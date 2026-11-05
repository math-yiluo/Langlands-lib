# Rational points of dynamic unipotent subgroups in unipotent normal subgroups: proof

Authors: Worker 1529 (proof route and Lean proof) and Worker 1524 (compilation fixes and
Markdown), for task `85a1a482-31f9-4e4d-9cc2-3099dd1be189`.

This module proves `Langlands.GroupScheme.PseudoReductiveRationalUnipotentPointStatement`,
stated in `Langlands.GroupScheme.Reductive.PseudoReductiveRationalUnipotentPointStatement`.
The theorem `Langlands.GroupScheme.pseudoReductiveRationalUnipotentPoint` has exactly that
proposition as its type, at an arbitrary universe `u`. Its kernel check uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`. No unproved statement is assumed.

## Main theorem

Let `k` and `K` be fields in universe `u` with `[Algebra k K]` (any extension), and write
`b = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k`. Let `G` be a group
scheme over `Spec k` with `IsPseudoReductive G`, let `χ : 𝔾_m ⟶ G` be a homomorphism, and
let `j : H ⟶ G_K` be a homomorphism into the base change `G_K` with `IsClosedSubgroup j`,
`IsUnipotent H` and `(SubgroupFunctor.range j).IsNormal`. Let `u` be a `k`-point of `G` with
`u ∈ U_G(χ)(k)`, that is, `Dynamic.HasLimit χ u 1`. If some `K`-point `y` of `H` satisfies

```lean
baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G
    (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (y ≫ j.hom.hom) = toUnit _ ≫ u
```

(the base change of `u` to `K` is a `K`-point of `H`), then `u = 1`.

The proof uses all four fields of `IsPseudoReductive G` (smoothness, affineness and
connectedness of `G` are needed to form the smooth connected normal closure below), and
the closedness, unipotence and normality of `H`. It uses no smoothness, reducedness or
connectedness of `H`, and no property of the extension `K / k`.

## Helper lemmas

Two lemmas in namespace `Langlands.GroupScheme.PseudoReductiveRationalUnipotentPoint`:

- `restrictionCore_isNormal`: for any base change `b : S' ⟶ S`, a group scheme `G` over `S`
  and a normal subgroup functor `F` of `G_{S'}`, the restriction core
  `SubgroupFunctor.restrictionCore b F` is normal in `G`. The restriction core (Library,
  `Langlands.GroupScheme.Derived.FieldBaseChangeProof`) consists of the points `g ∈ G(T)`
  such that for every `T'` over `S'` and every `c : T'_S ⟶ T`, the point `c ≫ g`, read as a
  point of `G_{S'}(T')` through `baseChangePointsEquiv`, lies in `F(T')`. Precomposition
  with `c` and the multiplicative equivalence `baseChangePointsEquiv` both preserve products
  and inverses, so the refinement of a conjugate `g x g⁻¹` is the conjugate of the
  refinement of `x`, which lies in `F` by normality of `F`.
- `mem_restrictionCore_of_baseChange`: under the hypothesis on `y` above, `u` lies in the
  restriction core of `range j` at the terminal object `Over.mk (𝟙 (Spec k))`. For `T'`
  over `K` and `c : T'_k ⟶ Over.mk (𝟙 (Spec k))`, `c` equals the image of `toUnit T'` under
  `Over.map b` followed by `toUnit _`, since both are morphisms to the terminal object. By
  naturality of `baseChangePointsEquiv` (`baseChangePointsEquiv_naturality`) and the
  hypothesis on `y`, the point `c ≫ u` is the image of `toUnit T' ≫ y ≫ j.hom.hom`, which
  lies in `range j`.

## Proof of the main theorem

Write `1` for the terminal object `Over.mk (𝟙 (Spec k))`.

1. *Descent of `H` to `k`.* Let `F = restrictionCore b (range j)`, a subgroup functor of
   `G`. Since `j` is a closed subgroup and `b` and `G` are affine,
   `SubgroupFunctor.restrictionCore_isClosedRepresentable` represents `F` by a closed
   subgroup `z : Z ⟶ G` over `k`. `F` is normal (`restrictionCore_isNormal`) and contains
   `u` (`mem_restrictionCore_of_baseChange`).
2. *A pointed morphism from `𝔾_m`.* Let `V = (Gm (Spec k)).X`, which is smooth, affine and
   geometrically integral over `k` (from `isSplitTorus_gm`). Let `w : V ⟶ G` be the constant
   morphism with value `u`, and
   `f = χ · w · χ⁻¹ · w⁻¹ : V ⟶ G`, that is, `f(t) = χ(t) u χ(t)⁻¹ u⁻¹`. Then `f(1) = 1`,
   and `f ∈ F(V)` because `F` is normal and contains `u`.
3. *The generated subgroup.* `ImageGeneration.pointedImageGeneration` gives a
   `GeneratedImage f`, that is, a closed subgroup `C ⊆ G` representing the intersection of
   all closed subgroups through which `f` factors, which is smooth, affine and geometrically
   connected over `k` (hence connected, since `Spec k` is a point). Since `f` factors
   through `z`, minimality gives `range C ≤ range z` (`GeneratedImage.range_le`).
4. *The normal closure.* Let `D = smoothConnectedNormalClosure C.inclusion`: a smooth,
   affine, connected closed subgroup of `G` with normal range containing `range C`. Since
   `Z` is a closed normal subgroup containing `C`, minimality gives `range D ≤ range z`
   (`SmoothConnectedNormalClosure.range_le`).
5. *`D` is unipotent.* Let `iK : D_K ⟶ G_K` be the base change of the inclusion of `D`.
   By `SubgroupFunctor.range_baseChangeHom` its range is the base change of `range D`,
   which lies in the base change of `F`, which lies in `range j`
   (`SubgroupFunctor.restrictionCore_baseChange_le`). So `iK = v ≫ j` for
   `v = IsRepresentedBy.factorHom` (module `Rational.LeviFactorization`). Since `iK` is a
   closed subgroup (`IsClosedSubgroup.baseChange`) and `j` is one, so is `v`
   (`IsClosedSubgroup.of_comp`). `H` is affine and locally of finite type over `K`, because
   `j` is a closed immersion into `G_K`. By `unipotentClosedSubgroup` the closed subgroup
   `D_K` of the unipotent `H` is unipotent, and by `IsUnipotent.of_baseChange` so is `D`.
6. *Pseudo-reductivity.* `HasTrivialUnipotentRadical G`, applied to `D` (closed, smooth,
   connected, unipotent, normal), gives `range D = ⊥`. Since `f` factors through `C`,
   `f ∈ range C(V) ≤ range D(V) = ⊥`, so `f = 1`.
7. *Conclusion.* From `f = 1`, `χ · w · χ⁻¹ = w` on `V`. Precomposing with the projection
   `1 ⊗ V ⟶ V` gives `Dynamic.orbit χ u = fst ≫ u`, that is, `u` lies in the dynamic
   centralizer `Z_G(χ)(k)`. Then `Dynamic.hasLimit_of_mem_centralizer` gives
   `HasLimit χ u u`, while the hypothesis is `HasLimit χ u 1`. `G` is affine, hence
   separated, so limits are unique (`Dynamic.HasLimit.unique`, module
   `Dynamic.Uniqueness`), and `u = 1`.

## Comparison with the suggested route

The task context suggests extending `s ↦ χ(s) u χ(s)⁻¹` to `c : 𝔸¹ ⟶ G` and generating a
normal subgroup from `(g, s) ↦ g c(s) g⁻¹` on `G × 𝔸¹`, with a schematic density argument
to see that its base change lies in `H`. The implemented proof instead works with the
morphism `f(t) = χ(t) u χ(t)⁻¹ u⁻¹` on `𝔾_m` and descends `H` to the closed normal
`k`-subgroup `Z` first, so that all minimality arguments take place over `k` and no
density argument is needed: the passage from `𝔾_m` to `𝔸¹` is handled by the uniqueness of
dynamic limits in a separated group.

## Provenance

Source: Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), registered
as `conrad-gabber-prasad-2015-pseudo-reductive` (PDF page = printed page + 26). The
statement generalizes the kernel step in the proof of Proposition C.1.6 (printed p.587, PDF
p.613): for `G` pseudo-reductive over `k = k_s` and `U = U_G(-λ)`, the kernel of
`U_{k̄} → G_{k̄}^{red}` has no nontrivial `k`-points, because it lies in `R_u(G_{k̄})` and a
nontrivial `k`-point would give infinitely many by `T(k)`-equivariance, contradicting
pseudo-reductivity. The proof here is not the source's argument: it replaces the
`T(k)`-orbit by the smooth connected normal `k`-subgroup generated by the morphism
`t ↦ χ(t) u χ(t)⁻¹ u⁻¹`, which is valid over any field `k`, any extension `K / k` and any
closed unipotent normal `H`.
