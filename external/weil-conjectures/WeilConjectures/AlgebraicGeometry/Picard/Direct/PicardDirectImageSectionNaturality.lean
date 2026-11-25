/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections

import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageSectionMapBijective
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageSectionMapRestriction

/-! # Natural section comparisons under successive base change

## References

* Stacks Project, Tags 0B91, 08HY and 0D5S
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The additive section comparison for a direct image is natural for arbitrary successive
base changes. -/
theorem picard_direct_image_section_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        picardDerivedModelSections E t ≃+
          Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            (c.app L).inv.app ⊤
              (((Modules.tensorPullback j).obj
                ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).presheaf.map
                  (homOfLE j.preimage_top.ge).op
                    (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                      ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).val.app
                        (Opposite.op ⊤) (q t ξ))) =
              q t' (picardDerivedModelRestriction E i t t' h ξ) := by
  classical
  refine ⟨fun t ↦ AddEquiv.ofBijective (picardDirectImageSectionMap f L W k t)
    (picardDirectImageSectionMap_bijective f L W k t), ?_⟩
  intro T T' i t t' h j hj₁ hj₂
  exact picardDirectImageSectionMap_restriction f L W k i t t' h j hj₁ hj₂

end AlgebraicGeometry.Scheme
