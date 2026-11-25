/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineSpectrumMateCompatibility
/-! # The base-change mate in affine spectrum coordinates

Source: Stacks Project, Tags 0DJ8, 08HY and 0D5S.
(blueprint: lem-pc-affine-spectrum-base-change-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Canonical spectrum coordinate transport identifies the actual base-change
comparison followed by the given coefficient morphism. No stalk condition is used.

Proof: write tY for the four canonical affine spectrum isomorphisms. Derived
pullback of tY and its inverse are mutually inverse: compose the canonical
pullback composition comparisons with the identity comparison. The pinned
derived adjunction therefore identifies RtY_* with L(tY.inv)^*. Naturality of tY
and these composition comparisons identify Rf_*K with LtS^* Rf0_*K0, and similarly
Rf'_*K' with LtS'^* Rf0'_*K0'. Compose the former identification with the pullback
comparison for g and tS to obtain eL; the latter gives eR. Expand the base-change
map as the Hom transpose under Lf'^* adjoint to Rf'_* of the square pullback
comparison followed by Lg'^* of the counit of f. Under the four equivalences,
coherence of pullback composition identifies the square comparison with that
for f0,f0',g0,g0'; naturality of adjunction counits identifies the following
counit. Naturality of the Hom transpose then identifies the base-change mates.
Finally apply naturality of the direct-image identification to phi. The map
on spectrum coordinates is exactly affineSpectrumDerivedMorphism by its
universal-composition definition, so the resulting equality is the displayed
one, including the coefficient map. These are categorical identities for
unbounded objects; empty schemes and zero rings require no separate argument.
Source: Stacks Project, Tag 0DJ8, affine reduction; Tag 08HY, counit definition of
base change; Tag 0D5S, derived pullback composition.
(blueprint: lem-pc-affine-spectrum-base-change-comparison). -/
theorem affineSpectrumCoordinates_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let K0 := affineSpectrumDerivedObject X K
    let K0' := affineSpectrumDerivedObject X' K'
    let φ0 := affineSpectrumDerivedMorphism g' K K' φ
    ∃ (eL : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj K) ≅
        (derivedPullback S'.toSpecΓ).obj
          ((derivedPullback (Spec.map g.appTop)).obj
            ((schemeDerivedDirectImage (Spec.map f.appTop)).obj K0)))
      (eR : (schemeDerivedDirectImage f').obj K' ≅
        (derivedPullback S'.toSpecΓ).obj
          ((schemeDerivedDirectImage (Spec.map f'.appTop)).obj K0')),
      schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
          (schemeDerivedDirectImage f').map φ =
        eL.hom ≫ (derivedPullback S'.toSpecΓ).map
          (schemeDerivedBaseChangeMap
              (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0.w K0 ≫
            (schemeDerivedDirectImage (Spec.map f'.appTop)).map φ0) ≫ eR.inv := by
  let T := derivedPullback S'.toSpecΓ
  let R0 := schemeDerivedDirectImage (Spec.map f'.appTop)
  let a := affineSpectrumBaseChangeSourceIso f g
  let b := affineSpectrumDerivedDirectImageIso f'
  have hb := affineSpectrum_baseChange_mate_compatibility f f' g g' sq.w sq0.w K
  let eL := a.app K
  let eR := b.app K'
  refine ⟨eL, eR, ?_⟩
  apply (cancel_mono eR.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := b.hom.naturality φ
  calc
    _ = schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
        b.hom.app ((derivedPullback g').obj K) ≫
          T.map (R0.map ((derivedPullback X'.isoSpec.inv).map φ)) := by
      change schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
        ((schemeDerivedDirectImage f').map φ ≫ b.hom.app K') = _
      rw [hn]
      rfl
    _ = eL.hom ≫ T.map
        (schemeDerivedBaseChangeMap (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0.w
            (affineSpectrumDerivedObject X K) ≫
          R0.map ((affineSpectrumDerivedPullbackIso g').hom.app K)) ≫
        T.map (R0.map ((derivedPullback X'.isoSpec.inv).map φ)) := by
      rw [← Category.assoc, hb, Category.assoc]
      rfl
    _ = _ := by
      simp only [affineSpectrumDerivedMorphism, Functor.map_comp, Category.assoc]
      rfl

end AlgebraicGeometry
