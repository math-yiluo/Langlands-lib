/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections

import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageSectionNaturality

/-! # Derived test sections of a base-changed direct image

## References

* Stacks Project, Tag 0B91, arbitrary base change
* Tag 08HY, canonical mate
* Tag 01IQ, residue fibre image
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Arbitrary base change identifies derived test sections of the direct image with
sections upstairs, and the identification respects the canonical fibre restriction.
This assertion has no perfect model, scalar basis, differential, or cycle hypothesis. -/
theorem picard_direct_image_test_sections
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        picardDerivedModelSections E t ≃+
          Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤),
      ∀ (V : W.Opens) (hwV : w ∈ V),
        ∃ j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k),
          (∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
            (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
              ∃ y, j y = x) ∧
          ∃ e : (Modules.tensorPullback j).obj
              ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) ≅
              (Modules.tensorPullback
                (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L,
            ∀ ξ : picardDerivedModelSections E V.ι,
              e.hom.app ⊤
                (((Modules.tensorPullback j).obj
                  ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).presheaf.map
                    (homOfLE j.preimage_top.ge).op
                      (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                        ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).val.app
                          (Opposite.op ⊤) (q V.ι ξ))) =
                q (W.fromSpecResidueField w)
                  (picardDerivedModelRestriction E (picardResidueLift W w V hwV) V.ι
                    (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV) ξ) := by
  classical
  obtain ⟨q, hq⟩ := picard_direct_image_section_naturality f L W k
  refine ⟨q, ?_⟩
  intro V hwV
  let i := picardResidueLift W w V hwV
  have hi : i ≫ V.ι = W.fromSpecResidueField w := picardResidueLift_comp W w V hwV
  let j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i) (by
      rw [Category.assoc, ← Category.assoc i, hi]
      exact pullback.condition)
  have hj₁ : j ≫ pullback.fst f (V.ι ≫ k) =
      pullback.fst f (W.fromSpecResidueField w ≫ k) := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd f (V.ι ≫ k) =
      pullback.snd f (W.fromSpecResidueField w ≫ k) ≫ i := pullback.lift_snd _ _ _
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (V.ι ≫ k)))).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (W.fromSpecResidueField w ≫ k))))).symm
    (Modules.pushforwardComp j (pullback.fst f (V.ι ≫ k)) ≪≫
      Modules.pushforwardCongr hj₁)
  let e := (c.app L).symm
  refine ⟨j, ?_, e, ?_⟩
  · intro x hx
    have hp : IsPullback j (pullback.snd f (W.fromSpecResidueField w ≫ k))
        (pullback.snd f (V.ι ≫ k)) i := by
      apply IsPullback.of_right _ hj₂ (IsPullback.of_hasPullback f (V.ι ≫ k))
      simpa only [hj₁, ← Category.assoc i, hi] using
        (IsPullback.of_hasPullback f (W.fromSpecResidueField w ≫ k))
    have hw : (⟨w, hwV⟩ : V.toScheme) ∈ Set.range i := by
      obtain ⟨z, hz⟩ : w ∈ Set.range (W.fromSpecResidueField w) := by
        rw [W.range_fromSpecResidueField]
        exact Set.mem_singleton w
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change V.ι (i z) = w
      rw [← Hom.comp_apply, hi, hz]
    obtain ⟨z, hz⟩ : x ∈ Set.range (pullback.fst (pullback.snd f (V.ι ≫ k)) i) := by
      rw [Scheme.Pullback.range_fst]
      change (pullback.snd f (V.ι ≫ k)) x ∈ Set.range i
      rw [hx]
      exact hw
    refine ⟨hp.isoPullback.inv z, ?_⟩
    rw [← Hom.comp_apply, hp.isoPullback_inv_fst, hz]
  · exact hq i V.ι (W.fromSpecResidueField w) hi j hj₁ hj₂

end AlgebraicGeometry.Scheme
