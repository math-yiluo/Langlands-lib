# The relative Weyl group as restrictions of absolute Weyl elements: proof

Author: Worker 216.

`Langlands.GroupScheme.relativeWeylAbsoluteRestriction` proves exactly the published
`Langlands.GroupScheme.RelativeWeylAbsoluteRestrictionStatement.{u}` (module
`Langlands.GroupScheme.Rational.RelativeWeylAbsoluteRestrictionStatement`) at an arbitrary
universe `u`, with no added hypothesis. This is Borel–Tits, *Groupes réductifs* (1965),
Corollaire 5.5; the statement's Markdown explains the correspondence with the source.

Notation as in the statement: `b = algebraBaseMap k K`, `G_K`, `S_K` and `i_K` are the actual
base changes along `b`, `j : T ⟶ G_K` is a maximal `K`-split torus and
`groupHom f ≫ j = i_K`. In the Lean file, inside the section `Extension`, local notations
`b`, `S_K` and `i_K` abbreviate `algebraBaseMap k K`, `(CommGroupScheme.baseChange b).obj` and
`(GroupScheme.baseChange b).map`.

The module proves four auxiliary results and then assembles the main theorem.

## `SubgroupFunctor.baseChangePointsEquiv_mem_normalizer`

A general lemma for any base morphism `b : S' ⟶ S`, group scheme `G` over `S` and subgroup
functor `F` of `G`. If a `T`-point `x` of `G_{S'}` (for `T` over `S'`) lies in the
normalizer of `F.baseChange b`, then the corresponding point
`baseChangePointsEquiv b G T x` of `G` over `(Over.map b).obj T` lies in the normalizer of
`F`.

Proof. Given `V` over `S`, a morphism `a : V ⟶ (Over.map b).obj T` and `y ∈ F(V)`, regard `V`
as a scheme `V'` over `S'` through `a.left ≫ T.hom`. Then `a` gives `a' : V' ⟶ T`, and the
identity of the underlying scheme gives an isomorphism `e : V ≅ (Over.map b).obj V'` with
`e.hom ≫ (Over.map b).map a' = a`. The point `y` transported to `V'` lies in
`F.baseChange b` (`mem_baseChange`). Applying the hypothesis on `x` at `a'` gives the two
conjugates (by `a' ≫ x` and by its inverse) in `F.baseChange b`. Rewriting with
`mem_baseChange`, multiplicativity of `baseChangePointsEquiv` and
`baseChangePointsEquiv_naturality`, and restricting along `e.hom` (`F.comp_mem`), gives the
two required memberships in `F(V)`.

## `exists_mul_of_mem_normalizerPoints_of_le_maximalSplitTorus` (conjunct 1)

This is a form of Borel–Tits 4.22, over an arbitrary field `K`. Let `G` be connected reductive
over `K`, `a : A ⟶ G` a split subtorus, `j : T ⟶ G` a maximal split torus and
`f : A ⟶ T` with `f ≫ j = a`. Every rational point `n ∈ normalizerPoints a` is `m * z` with
`m ∈ normalizerPoints a ⊓ normalizerPoints j` and `z ∈ centralizerPoints a`.

Proof. Let `σ` be the automorphism of `A` through which `n` normalizes `a`.

1. `torusNormalizerRepresentable` gives a closed subgroup `ζ : M ⟶ G` representing the
   centralizer `torusCentralizer a`, and `splitTorusCentralizerReductive` shows that `M` is
   connected reductive.
2. Both `j` and `j ≫ int(n)` are maximal split tori of `G` (`IsMaximalSplitTorus.comp_iso`).
   Both contain `a`: `j` through `f`, and `j ≫ int(n)` through `groupHom σ⁻¹ ≫ f`, since
   `a ≫ int(n) = σ ≫ a`. By `range_le_torusCentralizer_of_factor` both lie in the
   centralizer of `a`, so `IsMaximalSplitTorus.exists_lift` lifts them to maximal split tori
   `jM` and `j₁M` of `M` with `jM ≫ ζ = j` and `j₁M ≫ ζ = j ≫ int(n)`.
3. Rational conjugacy in `M` (`maximalSplitTorusConjugacy`, clause 1) gives a rational point
   `g` of `M` and an automorphism `e` of `T` with `j₁M ≫ int(g) = e ≫ jM`. Its image
   `g ≫ ζ` in `G` centralizes `a`: by `torusCentralizer_carrier_base` and the representation
   of the centralizer by `ζ`, it is in the range of `ζ`. Using `innerIso_hom_comp`
   (`ζ ≫ int(g ≫ ζ) = int(g) ≫ ζ`), `(j ≫ int(n)) ≫ int(g ≫ ζ) = e ≫ j`.
4. Put `m = (g ≫ ζ) * n`. By `innerIso_mul_hom`, `m` normalizes `j` through `e`, and by
   `IsNormalizingPoint.mul` it normalizes `a` through `σ`. Put `z = m⁻¹ * n`; then
   `n = m * z`, and `IsNormalizingPoint.inv` and `IsNormalizingPoint.mul` show that `z`
   normalizes `a` through `σ⁻¹ ≪≫ σ = 1`, so `z ∈ centralizerPoints a`.

The main theorem applies this lemma over `K` to `G_K` (connected reductive by
`connectedReductiveFieldExtensionStatement`), the split subtorus `i_K` (`IsSplitTorus.baseChange`
and `IsClosedSubgroup.baseChange`), `j` and `groupHom f`.

## `mem_centralizerPoints_of_baseChange_mapIso_eq_refl` (conjunct 3)

If `IsNormalizingPoint i n σ` and the base change of `σ` is the identity, then
`IsNormalizingPoint.baseChangeBasePoint` shows that the base-changed point normalizes `i_K`
through the identity, so `(GroupScheme.baseChange b).map (i ≫ int(n)) = i_K`
(`isNormalizingPoint_refl_iff`, `baseChange_innerIso_hom`). The pullback functor
`Over.pullback b` is faithful (`GaloisCocharacterDescent.faithful_algebraPullback`), so
`i ≫ int(n) = i`, which is `n ∈ centralizerPoints i` (`mem_centralizerPoints`).

## `exists_isNormalizingPoint_baseChange_mapIso` (inclusion `⊇` of conjunct 2)

Let `G` be connected reductive over `k`, `i` a maximal split torus, and `m` a `K`-point of
`G_K` with `IsNormalizingPoint i_K m τ`. Then there are a `k`-point `n` and `σ : S ≅ S`
with `IsNormalizingPoint i n σ` and `σ_K = τ`. This is where Borel–Tits 5.3 enters.

Proof. Let `U` be `Spec K` regarded over `Spec k` through `b`; it is connected.

1. `m` lies in `torusNormalizer i_K`, the normalizer of the range of `i_K`
   (`normalizerPoints_le_torusNormalizer`), and that range is the base change of the range of
   `i` (`SubgroupFunctor.range_baseChangeHom`). By the auxiliary lemma above, applied to the
   range of `i`, the corresponding `U`-point `m_U` of `G` lies in `torusNormalizer i` over `U`.
2. Surjectivity of `relativeWeylGroupRestrict i U` (`relativeWeylGroupRestrict_bijective`, the
   published Borel–Tits 5.3) gives `n ∈ normalizerPoints i` whose restriction to `U` has the
   same class as `m_U` modulo the centralizer (`relativeWeylGroupRestrict_mk`). Let `σ` be an
   automorphism through which `n` normalizes `i`.
3. The quotient `n_K⁻¹ * m`, where `n_K = baseChangeBasePoint b G n`, centralizes `i_K`: its
   `U`-point is the quotient from step 2, which lies in `torusCentralizer i` over `U`, and
   `torusCentralizer_baseChange` with `torusCentralizer_carrier_base` turns this into
   membership in `centralizerPoints i_K`.
4. By `IsNormalizingPoint.baseChangeBasePoint`, `n_K` normalizes `i_K` through `σ_K`; with
   `IsNormalizingPoint.mul`, `m = n_K * (n_K⁻¹ * m)` also normalizes `i_K` through `σ_K`.
   The underlying morphism of `i` is a closed immersion, hence a monomorphism, and so is that
   of `i_K`. `IsNormalizingPoint.unique` therefore gives `σ_K = τ`.

## `relativeWeylAbsoluteRestriction`

Conjunct 1 and conjunct 3 are the lemmas above. For conjunct 2:

- `⊆`: if `τ = σ_K` with `IsNormalizingPoint i n σ`, the base-changed point `n_K` normalizes
  `i_K` through `σ_K` (`IsNormalizingPoint.baseChangeBasePoint`). Conjunct 1 writes
  `n_K = m * z` with `m ∈ normalizerPoints j` and `z` centralizing `i_K`; then
  `m = n_K * z⁻¹` normalizes `i_K` through `σ_K` (`IsNormalizingPoint.inv`,
  `IsNormalizingPoint.mul`).
- `⊇`: `exists_isNormalizingPoint_baseChange_mapIso`.

## Published inputs

Proved statements:

- `torusNormalizerRepresentable` (`Langlands.GroupScheme.Rational.TorusNormalizerProof`)
- `splitTorusCentralizerReductive`
  (`Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof`)
- `maximalSplitTorusConjugacy` (`Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof`)
- `relativeWeylGroupRestrict_bijective`
  (`Langlands.GroupScheme.Rational.RelativeWeylGroupRestrictProof`)
- `connectedReductiveFieldExtensionStatement`
  (`Langlands.GroupScheme.Reductive.FieldExtensionProof`)

Other published theorems:

- `torusCentralizer_baseChange` (`Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction`)
- `GaloisCocharacterDescent.faithful_algebraPullback`
  (`Langlands.GroupScheme.Absolute.CocharacterDescentGroup`)
- `IsNormalizingPoint.baseChangeBasePoint` (`Langlands.GroupScheme.Rational.NormalizerGaloisAction`)
- `baseChange_innerIso_hom` (`Langlands.GroupScheme.Rational.SubgroupConjugacyDescent`)
- `range_le_torusCentralizer_of_factor`
  (`Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer`)
- `IsMaximalSplitTorus.exists_lift` (`Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup`)
- `IsMaximalSplitTorus.comp_iso` (`Langlands.GroupScheme.Rational.SplitRankTransport`)
- `innerIso_hom_comp` (`Langlands.GroupScheme.ConjugacyBaseChange`)
- `innerIso_mul_hom` (`Langlands.GroupScheme.InnerAutomorphismHom`)
- `SubgroupFunctor.range_baseChangeHom` and `IsClosedSubgroup.baseChange`
  (`Langlands.GroupScheme.SubgroupBaseChange`)
- `SubgroupFunctor.mem_baseChange` and `SubgroupFunctor.mem_range`
  (`Langlands.GroupScheme.SubgroupFunctor`)
- `IsSplitTorus.baseChange` and `baseChangePointsEquiv_naturality`
  (`Langlands.GroupScheme.Torus.Split`)
- `torusCentralizer_carrier_base` (`Langlands.GroupScheme.Rational.RelativeRoots`)
- `normalizerPoints_le_torusNormalizer` and `relativeWeylGroupRestrict_mk`
  (`Langlands.GroupScheme.Rational.TorusNormalizer`)
- `IsNormalizingPoint.mul`, `IsNormalizingPoint.inv`, `IsNormalizingPoint.unique`,
  `isNormalizingPoint_refl_iff` and `mem_centralizerPoints`
  (`Langlands.GroupScheme.Torus.Maximal`)

The definitions `baseChangePointsEquiv` (`Langlands.GroupScheme.Torus.Split`),
`baseChangeBasePointsEquiv` (`Langlands.GroupScheme.CocharacterTransport`) and
`baseChangeBasePoint` (`Langlands.GroupScheme.ConjugacyBaseChange`) are used through their
definitional unfolding. Mathlib lemmas (category theory, quotient groups) are used as well.

## Relation to the source

Borel–Tits derive Corollaire 5.5 from 4.22 (factorization of the normalizer of a split torus
through a maximal split torus containing it) and 5.3 (the relative Weyl group does not change
under field extension). The Lean proof follows that route: conjunct 1 is proved directly as the
4.22-type lemma above, using conjugacy of maximal split tori in the reductive centralizer, and
the `⊇` half of conjunct 2 uses the published 5.3 (`relativeWeylGroupRestrict_bijective`).
Conjunct 3 uses only faithfulness of base change along a field extension.
