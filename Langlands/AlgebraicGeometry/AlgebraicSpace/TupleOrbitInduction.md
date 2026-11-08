# The Noetherian case by induction over tuple-orbit covers

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitInduction`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

This module proves the Noetherian case of task 13a3a0fd, "AF representability from a finite
surjection with quasi-affine source". It assumes the reduced-closed-subspace statement.

The main theorem is `noetherianSchemeQuasiAffineSourceAF_of_reducedClosedSubspace`:

`ReducedClosedSubspaceStatement.{u} → NoetherianSchemeQuasiAffineSourceAFStatement.{u}`.

- `ReducedClosedSubspaceStatement` (published) has a proof task of its own, fb8256b4.
- `NoetherianSchemeQuasiAffineSourceAFStatement` (candidate 09f0ac49) says the following.
  Over any base `S`, let `Y` be a quasi-compact quasi-separated algebraic space with a finite
  surjective map from a quasi-affine Noetherian scheme `U`. Then `Y` is represented, by a
  natural isomorphism on all scheme tests, by a scheme in which every finite set of points
  lies in an affine open.

## Auxiliary results

Here `a : h_U ⟶ X` is a map from a represented presheaf to a presheaf on `Over S`. Points
are compared with the published `SameImage`.

- `sameImage_map_comp_iff φ a w w'`: for `φ : U' ⟶ U`, two points `w, w'` of `U'` have the
  same image under `h_φ ≫ a` iff `φ w` and `φ w'` have the same image under `a`. The proof
  applies the toolkit's `SameImage₂.of_comp_iff` on each side.
- `sameImage_comp_iso_iff a e u u'`: composing `a` with an isomorphism of presheaves
  `e : X ≅ X'` does not change `SameImage`. The witness is unchanged; one direction cancels
  the monomorphism `e.hom`.
- `sameImage_map_iff φ x x'`: for a morphism `φ : U ⟶ V` of schemes over `S`, `x` and `x'`
  have the same image under `h_φ` iff `φ x = φ x'`.
  - Forward: faithfulness of `schemeYoneda S` turns a witness into `g ≫ φ = g' ≫ φ`.
  - Backward: a point of the scheme pullback `U ×_V U` over `(x, x')` (Mathlib's
    `Scheme.Pullback.exists_preimage_pullback`) together with the toolkit's `overPullback`
    gives a witness.
- `IsFinite.comp_iso hf e`: a finite transformation followed by an isomorphism of presheaves
  is finite. Relative properties respect isomorphisms,
  `MorphismProperty.cancel_right_of_respectsIso`; this is the pattern of the Library's
  `IsSurjective.comp_iso`.
- `isFinite_left_of_isFinite_map φ h`: if `h_φ` is finite, then `φ.left` is finite. Apply the
  definition of finiteness to the identity-pullback square `IsPullback.of_id_fst`.
- `reducedOver U Z` and `reducedOverι U Z` (definitions): the reduced induced closed
  subscheme of `U.left` on a closed set `Z`, as a scheme over `S` with its inclusion. They are
  Mathlib's `Scheme.IdealSheafData.vanishingIdeal Z`, `subscheme` and `subschemeι`.
  - `reducedOverι_left` records the underlying morphism.
  - Two instances say that the inclusion is a closed immersion and that the subscheme is
    reduced (`ReducedSubscheme.isReduced_vanishingIdeal_subscheme`).
  - `range_reducedOverι` says the range is `Z`.

## One induction step: `exists_af_of_tupleOrbitCover`

Hypotheses:

- `U` is quasi-affine, and `f : h_U ⟶ Y` is finite and surjective;
- `T : TupleOrbitCover f` (module `TupleOrbitCover`), with fibre power `P`, closed
  permutation-stable set `Wset ⊆ P` and proper closed saturated set `C ⊆ U`;
- `PC` is a scheme over `S` with finite affine neighbourhoods;
- `q₀ : reducedOver U C ⟶ PC` has closed underlying map. For points `x, x'` of the reduced
  subscheme on `C`, their images in `U` have the same image under `f` iff `q₀ x = q₀ x'`.

Conclusion: `Y` is represented by a scheme with finite affine neighbourhoods.

Proof. Let `f₀ = h_{pr 0} ≫ f`, which is finite (`IsFinite.map_comp`). `P.obj` is
quasi-affine, being finite over `U` (`Scheme.IsQuasiAffine.of_isAffineHom`).

1. Relation. On points of `P.obj`, `rel w w'` holds iff one of the following does:
   - `w, w' ∈ Wset` and `SameImage f₀ w w'`;
   - `w, w' ∉ Wset` and `w' = perm σ w` for a permutation `σ`.

   This is an equivalence relation, since `perm` is a group action and `Wset` is
   permutation-stable. Its classes are finite: they lie in a `SameImage` class
   (`SameImage.finite_class`) or in a finite orbit. Each `perm σ w` is related to `w`. Inside
   `Wset` this is because `perm σ ≫ pr 0 = pr (σ 0)` and all projections have the same
   composite to `Y`.
2. Closed part. Let `Z` be the reduced subscheme of `P.obj` on the closed set
   `Wset ∩ pr 0⁻¹ C`, with closed immersion `i`. The composite `i ≫ pr 0` lands in `C`, so it
   lifts to `l : Z ⟶ reducedOver U C` (`ReducedSubscheme.exists_lift_vanishingIdeal`).
   - `l` is a closed map: `l '' K` is the preimage, under the injective inclusion of the
     reduced subscheme on `C`, of the closed set `pr 0 (i '' K)`.
   - Put `q = l ≫ q₀`, a closed map.
   - The range of `i` is `rel`-saturated, because `C` is saturated.
   - On the range of `i`, `rel (i z) (i z')` iff `q z = q z'`. Indeed, the left side is
     `SameImage f₀ (i z) (i z')`. By `sameImage_map_comp_iff` this is `SameImage f` of
     `pr 0 (i z)` and `pr 0 (i z')`, that is, of the images of `l z` and `l z'`. The
     hypothesis on `q₀` converts this to `q z = q z'`.
   - Off the range of `i`, related points differ by a permutation. Outside `Wset` this is the
     definition. In `Wset` with `pr 0 w ∉ C` it is `TupleOrbitCover.orbit`.
3. The published `OrbitSaturatedAffineOpen.exists_saturated_isAffineOpen` applies with
   `G = Perm (Fin (k + 1))` acting by `perm`. Every finite set of points of `P.obj` lies in a
   `rel`-saturated affine open.
4. Finite cover. Let `W_B` be the reduced subscheme of `P.obj` on `Wset`, with inclusion `ι`,
   and `g = h_ι ≫ f₀ : h_{W_B} ⟶ Y`.
   - `g` is finite.
   - `g` is surjective by the Library's `isSurjective_of_isPullback`, applied to the
     represented pullback of `g` along `f`. Its projection to `U` is surjective: by
     `TupleOrbitCover.surj`, each `u` has the same image as `pr 0 w` for some `w ∈ Wset`. The
     toolkit's `SameImage₂.exists_pullback` then gives a point of the pullback over `u`.
   - For a finite set `F` of points of `W_B`, step 3 gives a saturated affine open `V ⊇ ι F`.
     Its preimage `ι⁻¹ V` is affine, since `ι` is a closed immersion. It is
     `SameImage g`-saturated: by `sameImage_map_comp_iff`, points with the same image under
     `g` map to `rel`-related points of `Wset`.
5. Worker 336's `SaturatedAffineOpensRepresentation.exists_AF_representation_of_saturated_affine_opens`
   now gives the representation.

## The induction: `noetherianSchemeQuasiAffineSourceAF_of_reducedClosedSubspace`

Fix the data `S, U₀, Y₀, f₀` of the statement. By well-founded induction on closed subsets
`Z` of the Noetherian space `U₀` (`WellFoundedLT (Closeds U₀)`), we prove the following for
every `U` with a closed immersion `j : U ⟶ U₀` whose range lies in `Z`: every
quasi-compact quasi-separated algebraic space `Y` with a finite surjective
`f : U ⟶ Y` is AF-represented. The case `Z = ⊤`, `j = 𝟙` is the theorem.

In the step, `U` is quasi-affine (`Scheme.IsQuasiAffine.of_isAffineHom j`), Noetherian
(`isNoetherian_of_isFinite j`), and has a quasi-separated underlying space.

- If `U` is empty, `exists_AF_representation_of_saturated_affine_opens` applies directly to
  `f`, since every finite set of points lies in the affine open `⊥`.
- Otherwise `exists_tupleOrbitCover` gives `T`, with proper closed saturated `C ⊂ U`.
  1. The hypothesis `ReducedClosedSubspaceStatement` applies to `reducedOver U C`, which is
     reduced, closed in `U` and has saturated range `C`. It gives a quasi-compact
     quasi-separated space `Y_C` and a finite surjective `f_C`. Points of the reduced
     subscheme have the same image under `f_C` iff their images in `U` have the same image
     under `f`.
  2. The closed immersion `reducedOverι ≫ j` has range `j(C)`. This is strictly smaller than
     `Z`: a point `u ∉ C` gives `j u ∈ Z ∖ j(C)`, by injectivity of `j`. The induction
     hypothesis therefore represents `Y_C` by an AF scheme `PC`, via `e_C : h_{PC} ≅ Y_C`.
  3. Fullness of `schemeYoneda S` gives `q₀ : reducedOver U C ⟶ PC` with
     `h_{q₀} = f_C ≫ e_C⁻¹`. It is finite (`IsFinite.comp_iso`, then
     `isFinite_left_of_isFinite_map`), hence a closed map.
  4. By `sameImage_map_iff`, `sameImage_comp_iso_iff` and the identification property of
     `f_C`, the hypothesis of `exists_af_of_tupleOrbitCover` holds, and it concludes.

## Provenance

Internal. The route replaces the normalization, conductor and pushout argument of Gross,
*Tensor generators on schemes and stacks* (2017), proof of Proposition 3.5, Steps 2–3
(source `gross-tensor-generators-schemes-stacks-2017`), by tuple-orbit covers, saturated
affine opens and Noetherian induction on closed subsets. No source proof is transcribed.
