# Maximal tori meet normalized smooth connected subgroups in maximal tori

Worker 43. This module proves clause (i) of Conrad, *Reductive group schemes*, Exercise 5.5.1,
the first clause of `NormalSubgroupIntersectionStatement`
([`Rational.NormalSubgroupIntersectionStatement`](NormalSubgroupIntersectionStatement.md)),
over an arbitrary field. It does not prove clause (ii) of that statement (parabolic and
Borel subgroups). It adds no statements, definitions or axioms; all inputs are published
Library results.

All group schemes are over `Spec k` for a field `k : Type u`. "Range" is
`SubgroupFunctor.range`: the subgroup functor of points that factor through the given
homomorphism, on every test scheme over the base. `⊓` is the pointwise intersection, and
equality of subgroup functors is equality on every test scheme.

## Declarations

All three theorems are in the namespace
`Langlands.GroupScheme.NormalSubgroupIntersection`.

- `exists_torusIntersection_of_isNormal` (`k` algebraically closed). Let `H` satisfy
  `Smooth H.X.hom`, `IsAffineHom H.X.hom` and `ConnectedSpace H.X.left`. Let
  `f : T ⟶ H` satisfy `IsMaximalTorus f`, and let `r : N ⟶ H` satisfy
  `IsClosedSubgroup r`, `Smooth N.X.hom`, `ConnectedSpace N.X.left` and
  `(range r).IsNormal`. Then there are a commutative group scheme `S`, a homomorphism
  `sT : S ⟶ T` with `IsClosedSubgroup sT`, and `sR : S ⟶ N` with `IsMaximalTorus sR`,
  such that `sT ≫ f = sR ≫ r` and `range (sT ≫ f) = range f ⊓ range r`.
- `exists_torusIntersection_of_isNormalizedBy` (`k` algebraically closed). Same
  conclusion for `t : T ⟶ G` and `n : N ⟶ G`, where `G` only satisfies
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`, `t` is a maximal torus,
  `n` is a smooth connected closed subgroup, and normality is weakened to
  `(range n).IsNormalizedBy (range t)`.
- `torusIntersection` (any field). Let `G` satisfy `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`. Let `t : T ⟶ G` satisfy `IsMaximalTorus t`, and let `n : N ⟶ G`
  satisfy `IsClosedSubgroup n`, `Smooth N.X.hom`, `ConnectedSpace N.X.left` and
  `(range n).IsNormalizedBy (range t)`. Then there are a commutative group scheme `C`
  and `c : C ⟶ N` with `IsMaximalTorus c` and `range (c ≫ n) = range n ⊓ range t`.
  This is clause (i) of the target statement, for the given `G`, `T`, `t`, `N`, `n`.
  It does not use `ConnectedSpace G.X.left`. The witness is the published commutative
  intersection: `C = commutativeSubgroupIntersection t n` and
  `c = commutativeSubgroupIntersectionSnd t n`.

## Proof of `exists_torusIntersection_of_isNormal`

The argument follows Worker 1496's `exists_radicalTorusIntersection_of_complement`
([`Absolute.MaximalRankRadicalTorusIntersectionOfComplement`](../Absolute/MaximalRankRadicalTorusIntersectionOfComplement.md)).
There the unipotent-by-torus decomposition was assumed for `N` itself. Here it is used
only for a Cartan subgroup of `N`.

1. `N` is affine and locally of finite type, since it is closed in `H`. The torus `T` is
   split: `IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting`,
   using that `k` is algebraically closed.
2. A torus inside `T`. Take a maximal torus `s₀ : S₀ ⟶ N` (`exists_isMaximalTorus`).
   `exists_maximalTorus_extension_of_finiteType` gives a maximal torus `t₁ : T₁ ⟶ H` and
   `a : S₀ ⟶ T₁` with `a ≫ t₁ = s₀ ≫ r`. `maximalTorusConjugacy` gives a point `g` of
   `H` and an isomorphism `e : T₁ ≅ T` with `t₁ ≫ int(g) = e ≫ f`. Since `range r` is
   normal and represented by `r`, conjugation by `g` restricts to an automorphism
   `c := conjugateIso` of `N`. Put `sR := s₀ ≫ c` and `sT := a ≫ e`. Then
   `IsMaximalTorus sR` (`IsMaximalTorus.comp_iso`) and `sT ≫ f = sR ≫ r`. `sT` is a
   closed subgroup by `IsClosedSubgroup.of_comp`, since `f` and `sR ≫ r` are closed.
3. Cartan subgroup. `exists_isCartanSubgroup_of_isMaximalTorus` gives a closed subgroup
   `cN : C ⟶ N` with `IsCartanSubgroup cN` that represents `torusCentralizer sR`.
   `cartanStructure` makes `C` smooth, connected and nilpotent, hence solvable. The
   torus `sR` centralizes itself (`range_le_torusCentralizer`), so it factors as
   `sC ≫ cN = sR` (`exists_factor_of_range_le`), and `sC` is a maximal torus of `C`
   (`IsMaximalTorus.of_comp`). `solvableMaximalTorusSemidirect` gives a closed unipotent
   subgroup `u : U ⟶ C` such that `subgroupMultiplication u sC : U × S₀ ⟶ C`,
   `(x, y) ↦ x * y`, is an isomorphism of schemes.
4. `T` meets `U` trivially. Let `v := u ≫ cN ≫ r : U ⟶ H`. The intersection
   `subgroupIntersection f v` maps to `U` by a closed immersion, the base change of the
   closed immersion `f` (`subgroupIntersection_isPullback_scheme`). So it is unipotent by
   `unipotentClosedSubgroup`. Every homomorphism from a unipotent group to a split torus
   is trivial (`IsUnipotent.comp_eq_one_of_isSplitTorus`). Hence every point in both
   `range f` and `range v` is `1`.
5. The inclusion `range (sT ≫ f) ≤ range f ⊓ range r` is immediate from
   `sT ≫ f = sR ≫ r`. Conversely, let `x = y ≫ f = z ≫ r` on a test scheme `V`. The
   point `z` of `N` commutes with every point of the torus `sR`. This is checked after
   composing with the monomorphism `r`: the image of `z` lies in the commutative `T`,
   and so does the image of `sR`, since `sR ≫ r = sT ≫ f`. So `z` lies in
   `torusCentralizer sR = range cN`, and `z = z' ≫ cN`. Decompose
   `z' = (w₁ ≫ u) * (w₂ ≫ sC)` with the inverse of `subgroupMultiplication u sC`. Then
   `x = (w₁ ≫ v) * (w₂ ≫ sT ≫ f)`. Here `w₁ ≫ v = x * (w₂ ≫ sT ≫ f)⁻¹` lies in
   `range f` and in `range v`, so it is `1` by step 4. Hence `x = w₂ ≫ (sT ≫ f)` lies in
   `range (sT ≫ f)`.

## Proof of `exists_torusIntersection_of_isNormalizedBy`

`G` is affine because `G.X.hom` is affine over `Spec k`.

1. `hasClosedRepresentative_normalizer_centralizer_range n hn` gives a closed subgroup
   `m : M ⟶ G` that represents `(range n).normalizer`, the normalizer subgroup functor
   of `range n` (`SubgroupFunctor.normalizer`).
2. `ReducedSubgroup.exists_reducedIdentityComponent m hm` (for perfect `k`; its
   construction is the identity component of the reduced subgroup of `M`) gives `H` and
   `f : H ⟶ M`. With `ι := f ≫ m`: `ι` is a closed subgroup, `H` is smooth and
   connected, and every smooth connected closed subgroup `K ⟶ G` whose range lies in
   `range m` factors through `ι`.
3. `range t ≤ (range n).normalizer`: for a point `g` of `range t` and a refinement `a`,
   both `a ≫ g` and its inverse lie in `range t`, so the hypothesis `IsNormalizedBy`
   gives both conjugation conditions of the normalizer. Also
   `range n ≤ (range n).normalizer` (`SubgroupFunctor.le_normalizer`). A torus is smooth
   and connected (`IsTorus.smooth`, `IsTorus.connectedSpace`), so step 2 gives
   factorizations `eT ≫ ι = t` and `eN ≫ ι = n`.
4. `eT` is a maximal torus of `H` (`IsMaximalTorus.of_comp`) and `eN` is a closed
   subgroup of `H` (`IsClosedSubgroup.of_comp`). The range of `eN` is normal in `H`. For
   a point `g` of `H` and `y` of `N`, the image `g ≫ ι` lies in the normalizer of
   `range n`. So `(g ≫ ι) * (y ≫ n) * (g ≫ ι)⁻¹ = z ≫ n` for some `z`
   (`conj_mem_of_mem_normalizer`). Since `ι` is a monomorphism and a homomorphism,
   `g * (y ≫ eN) * g⁻¹ = z ≫ eN`.
5. `exists_torusIntersection_of_isNormal` applied to `eT` and `eN` in `H` gives `S`,
   `sT`, `sR` with `sT ≫ eT = sR ≫ eN` and `range (sT ≫ eT) = range eT ⊓ range eN`.
   Composing with `ι` gives `sT ≫ t = sR ≫ n`. For the range equality, let
   `x = y ≫ t = z ≫ n`. Then `y ≫ eT = z ≫ eN`, because both become `x` after the
   monomorphism `ι`. So `y ≫ eT` lies in `range (sT ≫ eT)`, and `x` lies in
   `range (sT ≫ t)`. The other inclusion is immediate.

## Proof of `torusIntersection`

Let `K := AlgebraicClosure k` and `b := Spec.map (CommRingCat.ofHom (algebraMap k K))`.

1. Base change to `K`. `G_K` is affine over `K` and locally of finite type, and `N_K` is
   smooth: these are base changes of the corresponding morphisms (`pullback.snd`). `N_K`
   is connected (`connectedSpace_baseChange_of_smooth_affine`), and `n_K` is a closed
   subgroup (`IsClosedSubgroup.baseChange`). `t_K` is a maximal torus by the forward
   direction of `maximalTorusBaseChange`, which uses `Smooth G.X.hom`. Normalization is
   preserved: `SubgroupFunctor.range_baseChangeHom` identifies the ranges of `t_K`, `n_K`
   with the base changes of `range t`, `range n`, and `IsNormalizedBy.baseChange`
   applies.
2. `exists_torusIntersection_of_isNormalizedBy` over `K` gives `S'`, `sT`, `sR` with
   `IsClosedSubgroup sT`, `IsMaximalTorus sR`, `sT ≫ t_K = sR ≫ n_K` and
   `range (sT ≫ t_K) = range t_K ⊓ range n_K`.
3. `isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange_representative`
   (Library, [`CommutativeSubgroupIntersectionComparison`](../CommutativeSubgroupIntersectionComparison.md))
   descends this to `IsMaximalTorus (commutativeSubgroupIntersectionSnd t n)` over `k`.
4. `commutativeSubgroupIntersection_condition` and
   `range_commutativeSubgroupIntersection` give
   `range (commutativeSubgroupIntersectionSnd t n ≫ n) = range t ⊓ range n`. This equals
   `range n ⊓ range t` pointwise by commutativity of `⊓`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014, registered as `conrad-2014-reductive-group-schemes`.
Exercise 5.5.1(i), p.182, states the result. The exercise gives no proof. The route
above (a Cartan subgroup of `N` with its unipotent-by-torus decomposition; the reduced
identity component of the normalizer of `N`; descent from the algebraic closure) was
chosen for this formalization from published Library results.
