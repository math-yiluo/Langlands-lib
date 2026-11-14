# Descent of invariant cocharacters along an arbitrary Galois extension

Authors: Worker 2094 (Lean), Worker 88 (Markdown).

Lean module: `Langlands.GroupScheme.Absolute.InfiniteGaloisCocharacterDescent`. Its declarations
are in the namespace `Langlands.GroupScheme.InfiniteGaloisCocharacterDescent`.

The Library already descends a Galois-invariant cocharacter `ν : Gm_K → G_K` of an affine
`k`-group scheme `G` to a cocharacter `Gm_k → G`. This is `GaloisCocharacterDescent.descend`,
in the modules `CocharacterDescent` and `CocharacterDescentGroup`. That construction assumes
that `K/k` is finite dimensional and Galois.

The proof of `UnramifiedTwistedFixedTranslationStatement` needs the same descent for an
infinite extension: `K` is the maximal unramified extension of the local field `F`. This module
repeats the Library construction assuming only `[IsGalois k K]`.

Finiteness was used in exactly one step, the descent of the Laurent coefficients. Here that
step uses Mathlib's `InfiniteGalois.mem_range_algebraMap_iff_fixed`: in a Galois extension,
finite or not, an element fixed by every automorphism lies in the image of `k`. Every other step
calls published Library lemmas that do not assume finiteness.

The source motivation is the one recorded in the Library modules: the descent of an invariant
cocharacter in Milne, *Algebraic Groups* (2017), Theorem 25.1. Extending it to infinite Galois
extensions is standard Galois descent of coefficients. It is an internal implementation step,
not a numbered result of a source.

## Statements

Throughout, `k` and `K` are fields in the same universe, `K` is a `k`-algebra, and `K/k` is
Galois (`IsGalois k K`). The extension may be infinite.

- `mem_range_extend_iff`: a Laurent polynomial `p ∈ K[T, T⁻¹]` lies in the range of the
  coefficient extension `LaurentGaloisDescent.extend k K` exactly when
  `LaurentGaloisDescent.conjugate k K σ p = p` for every `σ ∈ Aut(K/k)`.
- `descendRingHom` (built from the pointwise choice `descendValue`): let `A` be a commutative
  ring and `f : A →+* K[T, T⁻¹]` a ring homomorphism whose values are all fixed by every
  coefficient conjugation. Then `descendRingHom` is a ring homomorphism `A →+* k[T, T⁻¹]`.
  `extend_descendValue` and `extend_descendRingHom` say that its composite with `extend` is `f`.
- `descendAlgHom`, `extend_descendAlgHom`: the same for a `k`-algebra `A` and a `k`-algebra
  homomorphism `f`. The descended map is a `k`-algebra homomorphism, and its composite with
  `extend` is `f`.

Now let `G` be a group scheme over `Spec k` with affine structure morphism
(`IsAffineHom G.X.hom`). Let `ν : Gm_K → G_K` be a group-scheme homomorphism to the base change
`G_K`, with `hν : GaloisCocharacterDescent.IsInvariant k K G ν`. That proposition says that `ν`
is fixed by the published `transportCocharacter` for every `σ ∈ Aut(K/k)`.

- `descendedCoordinates`: the `k`-algebra map from the affine coordinate algebra of `G` to
  `k[T, T⁻¹]`, obtained by descending the Laurent coordinates `coordinates k K G ν`.
  `extend_comp_descendedCoordinates` says that extending its coefficients to `K` gives back
  `coordinates k K G ν`.
- `descendedPoint`: the corresponding `k[T, T⁻¹]`-point of `G`. `pointCoordinates_descendedPoint`
  records its coordinates. `extend_descendedPoint` says that its image under coefficient
  extension is the universal value `universalValue k K G ν` of `ν`.
- `descendedMorphism : Gm_k.X ⟶ G.X`: the scheme morphism defined by this point.
  `laurentPoint_descendedMorphism` records its value on the universal Laurent point.
  `baseChangedMorphism_descendedMorphism` and `pullback_descendedMorphism` say that its base
  change to `K` is the underlying morphism of `ν`, before and after the multiplicative-group
  comparison `Gm.baseChangeIso`. `descendedMorphism_isMonHom` says that it respects the group
  laws.
- `descend : Gm_k ⟶ G`: the descended group-scheme homomorphism.
- `baseChange_descend`:
  `(Gm.baseChangeIso b).inv ≫ (GroupScheme.baseChange b).map (descend k K G ν hν) = ν`, where
  `b = algebraBaseMap k K`.

## Proof

1. `mem_range_extend_iff`. The forward direction is the published
   `LaurentGaloisDescent.conjugate_extend`. For the converse, `extend` is
   `AddMonoidAlgebra.map` of `algebraMap k K`. By Mathlib's `AddMonoidAlgebra.range_map`, its
   range consists of the Laurent polynomials all of whose coefficients lie in the image of
   `algebraMap k K`. Fix an exponent `m`. Applying the coefficient at `m` to the invariance
   hypothesis shows that `p.coeff m` is fixed by every `σ`. Then
   `InfiniteGalois.mem_range_algebraMap_iff_fixed` puts `p.coeff m` in the image of `k`.
2. Ring and algebra descent. `descendValue x` is a chosen preimage of `f x` under `extend`. The
   identities for one, multiplication, zero and addition hold after applying `extend`, so they
   hold before, by the published injectivity `LaurentGaloisDescent.extend_injective`. Respect
   for `k` scalars in `descendAlgHom` is checked the same way: both sides extend to the constant
   Laurent polynomial `single 0 (algebraMap k K r)` (`f.commutes` and
   `AddMonoidAlgebra.mapRingHom_single`).
3. Coordinates and point. The published `coordinates_fixed` shows that every Laurent coordinate
   of the invariant `ν` is fixed by coefficient conjugation. So `descendAlgHom` applies to
   `coordinates k K G ν`. `descendedPoint` is the inverse image of the result under the
   coordinate equivalence `Lie.pointCoordinates G`. `extend_descendedPoint` follows by
   injectivity of this equivalence, its naturality `Lie.pointCoordinates_naturality`, and step 2.
4. Base change. `descendedMorphism` composes the descended point with the published Laurent
   presentation of `Gm_k` (`Gm.relativeLaurentIso`, `laurentAffineIso`).
   `baseChangedMorphism_descendedMorphism` cancels the Laurent presentation over `K` and the
   point equivalence `baseChangePointsEquiv`. This reduces it to the published comparison
   `baseChangedMorphism_universal` together with step 3. `pullback_descendedMorphism` follows by
   cancelling `Gm.baseChangeIso`.
5. Group laws. Pullback along `Spec K → Spec k` is faithful (published
   `faithful_algebraPullback`, which needs no finiteness). The pullback of `descendedMorphism`
   equals the composite of the group isomorphism `Gm.baseChangeIso` with the group homomorphism
   `ν`, so it is a monoid homomorphism. The published `isMonHom_of_faithfulMap` reflects this to
   `descendedMorphism`. `descend` bundles it with `Grp.homMk`. `baseChange_descend` follows from
   step 4 by `Grp.hom_ext`.
