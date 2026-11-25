/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.Algebra.Homology.SingleComplexAffineBaseChangeCore
import WeilConjectures.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenStalkCondition
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine source opens in the single-complex induction

Source: Stacks Project, Tags 0DJ8 and 0DJ9, affine case.
(blueprint: lem-pc-single-complex-open-affine).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The affine base case, with a source open in the coordinates used by induction.
Source: Stacks Project, Tag 0DJ9, affine-open paragraph, and Tag 0DJ8.
(blueprint: lem-pc-single-complex-open-affine).

Proof: The inverse image U' of the affine U is affine since both bases are affine.
Restriction preserves quasi-coherent cohomology and the stalk condition: the local
rings at points of an open subscheme are the original local rings, and the canonical
pullback composition maps transport phi to its restriction. Identify U, U', S, S'
with the spectra of their global section rings. Transport the cartesian square,
objects and phi along these isomorphisms. Apply singleComplexAffineBaseChange.
Naturality of the derived adjunction counits and pullback composition comparisons
identifies its comparison with singleComplexOpenComparison. Transport invertibility
back. For the empty affine open both derived categories are zero and the same
comparison is invertible. No boundedness hypothesis is used. -/
theorem singleComplexOpenComparison_affine
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U) := by
  have sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f')
      (U.ι ≫ f) g :=
    (IsPullback.of_hasPullback g' U.ι).flip.paste_vert sq
  have : IsAffine U.toScheme := hU
  have : IsAffine (pullback g' U.ι) := IsAffine.of_isPullback sqU
  let KU := (derivedPullback U.ι).obj K
  let KU' := (derivedPullback (pullback.fst g' U.ι)).obj K'
  let φU :=
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' U.ι) U.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := U.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' U.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' U.ι)).map φ
  have hKU := (derivedPullback_tensor_preserve_QCoh U.ι).1 K hK
  have hKU' := (derivedPullback_tensor_preserve_QCoh (pullback.fst g' U.ι)).1 K' hK'
  have hSU := singleComplexStalkCondition_open f f' g g' sq K K' φ h_stalk U sqU
  change IsIso (schemeDerivedBaseChangeMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι) sqU.w KU ≫
    (schemeDerivedDirectImage (pullback.fst g' U.ι ≫ f')).map φU)
  have sq0 : IsPullback (Spec.map (pullback.snd g' U.ι).appTop)
      (Spec.map (pullback.fst g' U.ι ≫ f').appTop)
      (Spec.map (U.ι ≫ f).appTop) (Spec.map g.appTop) :=
    sqU.of_iso (pullback g' U.ι).isoSpec U.toScheme.isoSpec S'.isoSpec S.isoSpec
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
  obtain ⟨K0, K0', φ0, hK0, hK0', hstalk, eL, eR, hcomp⟩ :=
    exists_singleComplexAffineSpectrumCoordinates (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU sq0 KU hKU KU' hKU' φU
  have hb := singleComplexAffineBaseChangeCore Γ(S, ⊤) Γ(U.toScheme, ⊤)
    Γ(S', ⊤) Γ(pullback g' U.ι, ⊤)
    (U.ι ≫ f).appTop.hom g.appTop.hom (pullback.snd g' U.ι).appTop.hom
    (pullback.fst g' U.ι ≫ f').appTop.hom
    sq0 K0 hK0 K0' hK0' φ0 (hstalk.mp hSU)
  have hb0 : IsIso
      (schemeDerivedBaseChangeMap (Spec.map (U.ι ≫ f).appTop)
        (Spec.map (pullback.fst g' U.ι ≫ f').appTop)
        (Spec.map g.appTop) (Spec.map (pullback.snd g' U.ι).appTop) sq0.w K0 ≫
        (schemeDerivedDirectImage (Spec.map (pullback.fst g' U.ι ≫ f').appTop)).map φ0) := hb
  rw [hcomp]
  infer_instance
end AlgebraicGeometry
