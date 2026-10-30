# Proof: the noetherian affine agreement locus from the noetherian seesaw

Author: Worker 766.

This module proves the published proposition
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedNoetherianOfSeesawStatement`:

```lean
theorem Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedNoetherianAffine_of_seesaw :
    RigidifiedClassesEqualizerClosedNoetherianOfSeesawStatement.{u}
```

That proposition is the implication
`NoetherianLineBundleSeesawStatement.{u} → RigidifiedClassesZariskiSeparatedStatement.{u} →
SmoothGeometricIntegrality.{u} → RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u}`.
The theorem proves this implication only. It proves none of the three hypotheses, so it does not
by itself prove `RigidifiedClassesEqualizerClosedNoetherianAffineStatement`.

## Provenance

The reduction follows the standard argument behind Stacks Project, *More on Morphisms*,
Lemma 37.33.4 (tag 0BF0), registered as `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`: the
locus where two line bundles agree is the locus where `L ⊗ L'⁻¹` comes from the base, and over
an abelian scheme the rigidification turns "comes from the base" into "is trivial". The Lean
proof, including the helper lemmas below, is original to this project. The three hypotheses
have their own provenance, described in their Markdown files.

## Helper declarations

Unless qualified below, helpers are in namespace `Langlands.AlgebraicGeometry.Picard`.

- `LocallyIsoOver f M N`, for `f : X ⟶ T` and `M N : X.Modules`: every point `τ` of `T` has an
  open neighbourhood `U` with `M.restrict (f ⁻¹ᵁ U).ι ≅ N.restrict (f ⁻¹ᵁ U).ι`. With `f` the
  second projection `(X ×_{Spec R} T) ×_T T' ⟶ T'`, this is exactly the right-hand side of the
  seesaw statement. That statement writes the condition out in full; it has no named
  definition.
- `nonempty_pullback_iso_of_restrict_iso` (Lemma A). If `M` and `N` become isomorphic on an open
  `V`, then they become isomorphic after pullback along any `a : X ⟶ Y` whose image lies in `V`.
  The proof factors `a` through `V.ι` with `IsOpenImmersion.lift`. It then transports the
  isomorphism with `Scheme.Modules.restrictFunctorIsoPullback`, `pullbackComp` and
  `pullbackCongr`.
- `LocallyIsoOver.of_pullback` (Lemma B). Let `φ : X ⟶ Y` be a map over `T`, and let `M'`, `N'`
  be isomorphic to the pullbacks of `M`, `N` along `φ`. Then local isomorphism of `M`, `N` over
  `T` gives local isomorphism of `M'`, `N'` over `T`. For a point and its neighbourhood `U`,
  apply Lemma A to the map `((φ ≫ f) ⁻¹ᵁ U).ι ≫ φ`, which lands in `f ⁻¹ᵁ U`.
- `LocallyIsoOver.of_iso`: a global isomorphism is a local one (take `U = ⊤`).
- The existing `Langlands.AbelianScheme.MumfordPicardZero.pullbackCompIso`, imported from
  `MumfordBundlePicardZeroReduction`, supplies the isomorphism from the pullback along `k`
  to the iterated pullback for `w : f ≫ g = k`. The proof reuses this declaration with
  explicit morphism arguments.
- `relativeMap c h`, for `h : T' ⟶ U` in `Over S`, is the base-change map
  `pullback T'.hom c ⟶ pullback U.hom c`. It is written with `pullback.lift`, and it is
  definitionally `(relativeSpace c).map h`. The lemmas `relativeMap_fst` and `relativeMap_snd`
  give its projections; they are used with `rw`, because `simp` does not apply
  `pullback.lift_fst` through the definition here.
- `toSeesawSpace c h` and `fromSeesawSpace c h` are maps in both directions, built with
  `pullback.lift`, between the member `pullback T'.hom c` of the relative family and the
  fibre product used by the seesaw, `pullback (pullback.snd c U.hom) h.left`. Their projection
  lemmas are `toSeesawSpace_fst/snd` and `fromSeesawSpace_fst/snd`. The lemma
  `fromSeesawSpace_map` computes the composite of `fromSeesawSpace c h` with `relativeMap c h`.
  The two maps are not shown to be inverse to each other; the proof does not need that.
- `locallyIsoOver_seesaw_iff`. For sheaves `M`, `N` on `(relativeSpace c).obj U`, the seesaw
  condition (local isomorphism over `h.left`, after pulling back to the seesaw fibre product
  through `pullbackSymmetry`) is equivalent to local isomorphism over
  `(relativeProjection c).app T'` of the pullbacks along `(relativeSpace c).map h`. Each
  direction is Lemma B, applied to `toSeesawSpace` and to `fromSeesawSpace` respectively. The
  needed sheaf isomorphisms come from the reused `MumfordPicardZero.pullbackCompIso` and
  `pullbackComp`.
- `classesPullback_mk_eq_iff`. This lemma assumes `RigidifiedClassesZariskiSeparatedStatement`.
  Let `A` be an abelian scheme over `S`, `h : T ⟶ U` in `Over S`, and `L`, `L'` rigidified
  families over `U`. Then the pullbacks of the classes `⟦L⟧`, `⟦L'⟧` along `h` are equal if and
  only if the pulled-back carrier sheaves are locally isomorphic over
  `(relativeProjection A.X.hom).app T`.
  - Forward: an isomorphism of rigidified line bundles is forgotten to its carrier sheaves, and
    `LocallyIsoOver.of_iso` applies.
  - Backward: choose for each point `τ` an open `V τ ∋ τ` and an isomorphism over it. The `V τ`
    form an open cover, hence an open cover of `T.left` by `openCoverOfIsOpenCover`. By Zariski
    separatedness it suffices to show that the classes agree after pullback to each `V τ`. The
    map `(relativeSpace A.X.hom).map k`, for `k := Over.homMk (V τ).ι`, lands in the preimage of
    `V τ` by naturality of `relativeProjection`. Lemma A then gives an isomorphism of the
    underlying sheaves there. This is an isomorphism of line bundles (`ObjectProperty.isoMk`).
    `RigidifiedLineBundle.nonempty_iso_of_forget_iso` turns it into an isomorphism of
    rigidified line bundles; that lemma uses the published
    `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`, the relative projection and the
    section identity `relativeSection_projection`. `Quotient.sound` finishes.

## Proof of the main theorem

Introduce the hypotheses `seesaw`, `separated` and `integrality`. Fix a noetherian ring `R`, an
abelian scheme `A` over `Spec R` and classes `q`, `r`, and choose representatives `L`, `L'` by
`Quotient.inductionOn`.

1. `GeometricallyIntegral A.X.hom`. By `GeometricallyIntegral.iff_geometricallyIntegral_fiber`
   it suffices to treat each fibre `A.X.hom.fiberToSpecResidueField s`. That map is smooth and
   geometrically connected, by base change (`MorphismProperty.pullback_snd`) from the smoothness
   and geometric connectedness fields of `A`. Then `integrality` applies. The proof uses
   `set_option backward.isDefEq.respectTransparency.types false`, so that
   `MorphismProperty.pullback_snd` unifies with `fiberToSpecResidueField`.
2. The global-functions hypothesis of the seesaw. For an `R`-algebra `B`, the base change
   `pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R B)))` is smooth, proper and
   geometrically connected; Mathlib's base-change instances supply these properties. The
   published theorem `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` with
   `U = ⊤` makes its `app ⊤` an isomorphism, so its `appTop` is bijective
   (`ConcreteCategory.bijective_of_isIso`).
3. Apply `seesaw` with `c = A.X.hom` and `T = Spec R`, which is locally noetherian because `R`
   is noetherian. Take `t = (Over.mk (𝟙 (Spec R))).hom` and, for the two sheaves, the carriers of
   `L` and `L'` pulled back along `(pullbackSymmetry A.X.hom t).hom`. They are locally free of
   rank one because that property is stable under pullback (`.property.pullback`). This gives
   `Z`, a closed immersion `ι : Z ⟶ Spec R` and the factorisation criterion `hZ`.
4. For `h : T' ⟶ Over.mk (𝟙 (Spec R))`, chain three equivalences: `hZ h.left` (factorisation
   through `ι` ⟺ the seesaw condition), `locallyIsoOver_seesaw_iff` (seesaw condition ⟺ local
   isomorphism on the relative family), and `classesPullback_mk_eq_iff` with `separated` (local
   isomorphism ⟺ equality of the pulled-back classes).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Use

Combined with proofs of the three hypotheses, the theorem proves
`RigidifiedClassesEqualizerClosedNoetherianAffineStatement`, the target of task
`00ab6acd-8b6c-4595-8df8-3fbdac0bdd4d`. The noetherian seesaw is ported from the Anthropic FLT
Lean source in that task. Zariski separatedness is task `f34bab0f-25a2-40c7-a05c-6c0f06ed4283`,
and smooth geometric integrality is task `13d3f4b1-fadd-43c6-b422-d793dc9adf5f`.
