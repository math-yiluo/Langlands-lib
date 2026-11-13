# Mumford maps hit every dual point over the ample-fibre locus

This helper module, in namespace `Langlands.AbelianScheme`, works over an arbitrary base scheme
`S` and an abelian scheme `A` over `S`. It shows that every point of the chosen dual
`dualScheme A hA` lying over the ample-fibre locus of a line bundle is in the image of the
corresponding Mumford map. All results are internal helper lemmas, written for the proof of
`RelativeDualSchemeQuasiCompactStatement` in `RelativeDualSchemeQuasiCompactProof`.

Two published statements appear as explicit hypotheses:

- `preservation : pullbackTensorComparisonIsIsoStatement.{u}`, so that pullback commutes with
  tensor products of line bundles;
- `square : MumfordBundlePicardZeroStatement.{u}`, the theorem-of-the-square input, which
  `mumfordSchemeMap` needs.

The main proof instantiates them with the published proofs `pullbackTensorComparisonIsIso` and
`mumfordBundlePicardZero`.

## Results

- `relativeMumfordPointComparison preservation A L M evaluation K b a x hx Q premise`.
  Take a field `K` and a field-valued point `b : Spec K ⟶ S`. Take a lift `a : Over.mk b ⟶ A.X`,
  and a `K`-point `x` of the base change `(baseChange b).obj A` with
  `x.left ≫ pullback.fst = a.left`. Take a rigidified family `Q` over `Over.mk b`. Assume the line
  bundle underlying `Q` is isomorphic to the tensor product of two bundles: the pullback of `L`
  (base-changed to `A_K`) along translation by `x`, and the base change of `M`. Then the
  rigidified relative pullback of the Mumford bundle `mumfordBundle A preservation L M evaluation`
  along `a` is isomorphic to `Q`. The proof builds a carrier isomorphism with the published
  `FieldMumfordPoint.carrierIso`, using `fieldLineBundleTriviality` to trivialise the pullback of
  `M` along `a`. It then upgrades this to an isomorphism of rigidified bundles with
  `RigidifiedLineBundle.isoOfCarrierIso`.
- `relativeMumfordLift preservation square A L M evaluation hA K b p hLK`. Let `K` be
  algebraically closed, `b : Spec K ⟶ S`, and `p : Over.mk b ⟶ dualScheme A hA`. Suppose the
  pullback of the bundle underlying `L` to `A ×_S Spec K` is ample. Then there is
  `a : Over.mk b ⟶ A.X` with `a ≫ mumfordSchemeMap preservation square A L M evaluation hA = p`.
  The proof runs as follows:
  1. Let `Q` be the pullback of `poincareFamily A hA` along `p`, and `P` its line bundle on the
     base change `A_K`.
  2. `poincare_point_translation_invariant` shows that `P` is translation invariant.
  3. The published `algClosedFieldTranslationDifferenceLifting`, applied to the base changes of
     `L` and `M` and to the base change of `evaluation`, gives a point `x` of `A_K` with
     `t_x^* L_K ⊗ M_K ≅ P`.
  4. `exists_point_of_baseChangeSection` turns `x` into `a`.
  5. `relativeMumfordPointComparison` identifies the pullback of the Mumford family along `a`
     with `Q`.
  6. `mumford_point_eq_of_iso`, which uses the universal property of `dualScheme`, gives
     `a ≫ mumfordSchemeMap … = p`.
- `isAmple_pullback_of_mem_ampleFibreLocus f L K b hb`. Let `f : X ⟶ S`, and let
  `b : Spec K ⟶ S` send the closed point into `ampleFibreLocus f L`. Then the pullback of `L`
  along `pullback.fst f b` is ample. The proof uses `mem_ampleFibreLocus_iff_of_isPullback` for
  the square defining `X ×_S Spec K`. It then uses `isAmple_pullback_iff_of_field_isPullback` for
  the fibre over the closed point of `Spec K`.
- `isAmple_pullback_tensor_base preservation f L B K b hL`. Over a field point `b`, ampleness of
  the pullback of `L` implies ampleness of the pullback of `L ⊗ f^* B` for any line bundle `B` on
  `S`. The pullback `b^* B` is trivial by `fieldLineBundleTriviality`. The resulting chain of
  isomorphisms identifies the two pulled-back bundles, and `IsAmple.of_iso` concludes.
- `mem_range_mumfordSchemeMap preservation square A L M evaluation hA y hy`. Let `y` be a point
  of `(dualScheme A hA).left` whose image in `S` lies in the ample-fibre locus of the bundle
  underlying `L`. Then `y` is in the range of `(mumfordSchemeMap … hA).left`. The proof takes
  `Ω = AlgebraicClosure κ(y)` and the geometric point `g : Spec Ω ⟶ dualScheme` through
  `fromSpecResidueField y`, with `b = g ≫ (dualScheme A hA).hom`.
  `isAmple_pullback_of_mem_ampleFibreLocus` supplies the ampleness hypothesis.
  `relativeMumfordLift` gives `a` with `a ≫ mumfordSchemeMap … = Over.homMk g`. Evaluating at
  the closed point of `Spec Ω` gives a preimage of `y`.
- `mem_range_mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA
  y hy`. This is the same statement for `mumfordSchemeMapOfLineBundle`, which first normalises an
  ordinary line bundle `L` along the unit section via `LineBundle.normalize`. The bundle
  underlying the normalised bundle is `L ⊗ (A.X.hom)^* B`. Here the hypothesis concerns
  `ampleFibreLocus A.X.hom L` for the ordinary bundle `L`, and `isAmple_pullback_tensor_base`
  supplies the twist. The rest of the proof is the same as for `mem_range_mumfordSchemeMap`.

## Provenance

These lemmas are internal and relative versions of the published field-level surjectivity
argument in `FieldDualSchemeSurjectionProof`. Every point of `Pic⁰` of an abelian variety over an
algebraically closed field has the form `t_x^* L ⊗ L^{-1}` for an ample `L`. This is the cited
mathematical content of the published `AlgClosedFieldTranslationDifferenceLiftingStatement`;
see its Markdown for the literature. No new mathematics beyond that statement is claimed here.
