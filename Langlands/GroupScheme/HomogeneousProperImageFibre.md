# Proper images in fibres of invariant affine-valued maps on homogeneous spaces

Module `Langlands.GroupScheme.HomogeneousProperImageFibre`.

Workers 1095 and 1506. Worker 1506 wrote the predicate and the two theorem
statements, and sketched the proof route. Worker 1095 wrote the Lean proofs.

Throughout, `k` is a field, `Spec k` means `Spec (CommRingCat.of k)`, and a
rational point of a `k`-scheme `O` is a morphism `Over.mk (𝟙 (Spec k)) ⟶ O` over
`Spec k`.

## Selected definition

The record's selected declaration is
`Langlands.GroupScheme.HasOnePointProperImages H`, for a group scheme `H` over
`Spec k`. It is the proposition that, for every `k`-scheme `O` such that

- `O` is reduced, and its structure map is separated, locally of finite type and
  quasi-compact,
- `a : SchemeAction H O` is an action whose rational points form one orbit of
  the rational points of `H`: there is a rational point `x` of `O` such that every
  rational point `y` of `O` is `a.act g x` for some rational point `g` of `H`,

and every `k`-scheme `Z` that is proper over `k`, reduced and connected, the
underlying set of the image of every morphism `j : Z ⟶ O` over `k` has at most
one element.

So `H` "sends every proper connected reduced scheme to one point of each of its
homogeneous spaces". Transitivity is required only on rational points, and the
predicate says nothing about the action on other test schemes. No
algebraic closedness of `k` and no hypothesis on `H` is part of the definition.

## Main results

`HasOnePointProperImages.subsingleton_range_of_fibres`. Let `k` be
algebraically closed and let `N` be a group scheme over `Spec k` whose structure
map is smooth and which satisfies `HasOnePointProperImages N`. Let `O` be a
`k`-scheme that is reduced, separated, locally of finite type and quasi-compact
over `k`, with an action `b : SchemeAction N O`. Let `W` be a `k`-scheme with
affine underlying scheme and `f : O ⟶ W` a morphism over `k`. Assume:

- `hf`: `f` is invariant on rational points: `b.act n y ≫ f = y ≫ f` for all
  rational points `n` of `N` and `y` of `O`;
- `horb`: each rational fibre of `f` is one orbit: if rational points `y`, `z` of
  `O` satisfy `y ≫ f = z ≫ f`, then `b.act n y = z` for some rational point `n`
  of `N`.

Then for every proper, reduced and connected `k`-scheme `Z` and every
`j : Z ⟶ O`, the image of `j` has at most one point.

The theorem does not assume that `N(k)` acts transitively on the rational
points of `O`.

`hasOnePointProperImages_of_range_id_eq_bot`. Let `k` be algebraically closed
and `H` a group scheme over `Spec k` with `SubgroupFunctor.range (𝟙 H) = ⊥`,
that is, every point of `H` on every test scheme is the identity. Then
`HasOnePointProperImages H` holds. The proof shows more: each `O` in the
predicate has exactly one underlying point. This uses only that `O` is locally
of finite type over `k`. It does not use reducedness, separatedness or
quasi-compactness of `O`, or any property of `Z`.

## Provenance

This is internal glue for the proof of
`Langlands.GroupScheme.SolvableOrbitProperImageFiniteStatement`. That proof
follows Milne, *Algebraic Groups* (2017), Theorem 17.1 and the argument around
it. It is an induction along a split-solvable series. In the induction step a
normal subgroup `N` of `G` acts on a homogeneous space `O = G/H`, and `O` has an
`N`-invariant map to an affine scheme `W` whose rational fibres are `N`-orbits.
This module proves that step: it reduces the image of a proper connected scheme
in `O` to its image in one fibre, where the induction hypothesis on `N`
applies. The base case of the induction is the trivial group. The predicate
`HasOnePointProperImages` is the induction hypothesis chosen for the Lean proof.
It is not a definition from the literature. Constructing `W` and `f`, proving
`hf` and `horb`, and running the induction are done in Worker 1506's modules for
the same task, not here.

## Proof of `subsingleton_range_of_fibres`

1. **A rational point of `Z`.** `Z` is connected, hence nonempty, and, being
   proper, locally of finite type over the algebraically closed field `k`. So it
   has a rational point `z0` (`nonempty_rationalPoints`).

2. **`j ≫ f` is constant.** Set `w0 = z0 ≫ j ≫ f`, a rational point of `W`.
   `Langlands.AlgebraicGeometry.affineMap_eq_constant_of_proper_connected_reduced`
   gives `(j ≫ f).left = Z.hom ≫ w0.left`, because `W.left` is affine. Since
   `w0.left` is a section of `W.hom`, Mathlib's `isClosedImmersion_of_comp_eq_id`
   makes it a closed immersion. In particular its image, one point of `W`, is
   closed.

3. **The fibre is closed and invariant.** Let `C = f.left ⁻¹' range w0.left`, a
   closed subset of `O`. For a rational point `n` of `N`, the translation
   `b.translation n ≫ f` and `f` agree on all rational points of `O`, by
   `SchemeAction.comp_translation` and `hf`. `O` is reduced and locally of finite
   type, and `W` is separated over `k` because `W.left` and `Spec k` are affine.
   So `hom_ext_rationalPoints` gives
   `b.translation n ≫ f = f`. Hence every rational translation maps `C` into
   itself (`SchemeAction.IsInvariantClosed`).

4. **The reduced fibre and its action.** `N` is smooth, so
   `SchemeAction.exists_reduced_invariantClosedSubscheme` gives a reduced
   `k`-scheme `O'`, a morphism `incl : O' ⟶ O` whose underlying map is a closed
   immersion with image `C`, and an action `b'` of `N` on `O'` with
   `b'.act n o ≫ incl = b.act n (o ≫ incl)` on every test. Composing the
   structure map with the closed immersion makes `O'` separated, locally of finite
   type and quasi-compact over `k`, and `incl` is a monomorphism over `k`.

5. **Lifting `j`.** The image of `j` lies in `C` by step 2. `Z` is reduced, so
   `FiniteIndexTransfer.exists_lift_of_range_subset` factors `j.left` through
   `incl.left`. This gives `j' : Z ⟶ O'` over `k` with `j' ≫ incl = j` on
   underlying schemes.

6. **`incl ≫ f` is constant.** The image of `(incl ≫ f).left` lies in the image
   of `w0.left`, so the same lifting lemma, applied to the closed immersion
   `w0.left` and the reduced scheme `O'`, factors `(incl ≫ f).left` through
   `w0.left`. The factor `O'.left ⟶ Spec k` is `O'.hom`: compose both sides with
   `W.hom`. Hence `(y ≫ incl) ≫ f = w0` for every rational point `y` of `O'`.

7. **The fibre is homogeneous.** Put `x' = z0 ≫ j'`. For a rational point `y` of
   `O'`, step 6 gives `(x' ≫ incl) ≫ f = (y ≫ incl) ≫ f`, so `horb` gives `n`
   with `b.act n (x' ≫ incl) = y ≫ incl`. By the compatibility in step 4 this is
   `b'.act n x' ≫ incl = y ≫ incl`. Cancelling the monomorphism `incl` gives
   `b'.act n x' = y`.

8. **Conclusion.** `hN` applied to `O'`, `b'`, `x'`, `Z` and `j'` shows that
   the image of `j'` has at most one point. The image of `j` is the image of `j'`
   under `incl.left`, so it also has at most one point.

## Proof of `hasOnePointProperImages_of_range_id_eq_bot`

Every rational point `g` of `H` lies in `SubgroupFunctor.range (𝟙 H)`, which is
`⊥`, so `g = 1`. Hence every rational point of `O` is `a.act 1 x = x`
(`SchemeAction.act_one`). `O` is locally of finite type over the algebraically
closed field `k`, so each closed point `w` of `O` is the image of a rational
point (`pointOfClosedPoint`). That rational point equals `x`, so
`w = x.left (closedPoint)`. The point of `x` is closed (`pointEquivClosedPoint`),
and `O` is a Jacobson space, so its closed points are dense
(`closure_closedPoints`). Therefore every point of `O` is the point of `x`, and
every subset of `O`, in particular the image of `j`, has at most one element.

## Declarations

- `Langlands.GroupScheme.HasOnePointProperImages` (definition, selected).
- `Langlands.GroupScheme.HasOnePointProperImages.subsingleton_range_of_fibres`.
- `Langlands.GroupScheme.hasOnePointProperImages_of_range_id_eq_bot`.
