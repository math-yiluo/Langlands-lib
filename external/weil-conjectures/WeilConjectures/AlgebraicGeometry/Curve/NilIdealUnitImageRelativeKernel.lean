/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsEpi

/-! # The image of nil-ideal units is the pushforward of the relative unit kernel.

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-nil-ideal-unit-image-relative-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private lemma epi_gmSheafToLowerStar_nilIdeal (X : Scheme.{u})
    (J : X.IdealSheafData) (hJN : J ≤ X.nilradical) :
    Epi (gmSheafToLowerStarGmSheaf J.subschemeι) := by
  have : Surjective J.subschemeι := by
    constructor
    rw [← Set.range_eq_univ, IdealSheafData.range_subschemeι]
    apply Set.eq_univ_of_univ_subset
    change (X.nilradical.support : Set X) ⊆ (J.support : Set X)
    exact IdealSheafData.support_antitone hJN
  have := locallySurjective_gmSheafToLowerStar_of_thickening J.subschemeι
  exact Sheaf.epi_of_isLocallySurjective (gmSheafToLowerStarGmSheaf J.subschemeι)

private lemma gmSheafToLowerStar_comp {X Y Z : Scheme.{u}}
    (j : Z ⟶ Y) (i : Y ⟶ X) (ij : Z ⟶ X) (hij : ij = j ≫ i) :
    gmSheafToLowerStarGmSheaf i ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} i).map
          (gmSheafToLowerStarGmSheaf j) ≫
        (Etale.lowerStarComp AddCommGrpCat.{u + 1} j i ij hij).hom.app Z.gmSheaf =
      gmSheafToLowerStarGmSheaf ij := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ ≫
      CommRingCat.unitsAddCommGrpULift.map _ ≫
      CommRingCat.unitsAddCommGrpULift.map _ =
    CommRingCat.unitsAddCommGrpULift.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change (pullback.fst V.unop.hom i).appTop ≫
      (pullback.fst (pullback.snd V.unop.hom i) j).appTop ≫
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        j i ij hij).hom.app V.unop).left.appTop =
    (pullback.fst V.unop.hom ij).appTop
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
  congr 1
  simp [MorphismProperty.Over.pullbackComp]

private lemma image_kernel_comp_iso {C : Type*} [Category C] [Abelian C]
    {A B D E : C} (p : A ⟶ B) (r : B ⟶ D) (q : A ⟶ E) (e : D ≅ E)
    (h : p ≫ r ≫ e.hom = q) [Epi p] :
    Nonempty (image (kernel.ι q ≫ p) ≅ kernel r) := by
  have w : p ≫ r = q ≫ e.inv := by rw [← h]; simp
  let k : kernel q ⟶ kernel r := kernel.map q r p e.inv w.symm
  have hk : k ≫ kernel.ι r = kernel.ι q ≫ p := by simp [k]
  let s : PullbackCone p (kernel.ι r) := PullbackCone.mk (kernel.ι q) k hk.symm
  have hs : IsLimit s := by
    refine PullbackCone.IsLimit.mk _
      (fun t => kernel.lift q t.fst ?_) ?_ ?_ ?_
    · rw [← h, ← Category.assoc, t.condition, Category.assoc, kernel.condition_assoc,
        zero_comp, comp_zero]
    · intro t
      exact kernel.lift_ι _ _ _
    · intro t
      apply (cancel_mono (kernel.ι r)).1
      simp only [Category.assoc, hk, kernel.lift_ι_assoc]
      exact t.condition
    · intro t m hm₁ _hm₂
      apply (cancel_mono (kernel.ι q)).1
      simpa only [kernel.lift_ι] using hm₁
  have : Epi k := Abelian.epi_snd_of_isLimit p (kernel.ι r) hs
  have : StrongEpi k := strongEpi_of_epi k
  exact ⟨(image.isoStrongEpiMono k (kernel.ι r) hk).symm⟩

/-- The image of nil-ideal units is the pushforward of the relative unit kernel.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-nil-ideal-unit-image-relative-kernel)

Proof: Since J ≤ I ≤ the nilradical, the closed immersion of the J subscheme
is surjective on points. After base change to an affine etale object it is
surjective on functions. Any lift of a unit is a unit: its basic open pulls
back to the whole source, hence is the whole target by surjectivity on points.
The affine open cover therefore makes the map p from Gm_X to (i_J)_*Gm_J
locally surjective, so it is epi. Put r = (i_J)_*q_j. Pullback pasting gives an
isomorphism e identifying p followed by r with q_I. The induced map
ker(q_I) to ker(r) is the pullback of p along the kernel inclusion, so it is
epi in the abelian category of sheaves. Its factorization followed by the
kernel inclusion is the displayed map. Uniqueness of strong epi-mono image
factorizations identifies its image with ker(r). Finally direct image
preserves kernels, identifying ker(r) with (i_J)_*ker(q_j).
This argument needs only J to be nil; the given hypotheses imply that.
For I=J or I=0 both sides are zero. The empty affine object causes no
exception: functions and units are trivial and the empty cover is covering. -/
theorem nonempty_nilIdealUnitImageRelativeKernelIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hIN : I ≤ X.nilradical) :
    Nonempty (image (kernel.ι (gmSheafToLowerStarGmSheaf I.subschemeι) ≫
        gmSheafToLowerStarGmSheaf J.subschemeι) ≅
      (Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι).obj
        (kernel (gmSheafToLowerStarGmSheaf (IdealSheafData.inclusion hJI)))) := by
  let F := Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι
  let r := gmSheafToLowerStarGmSheaf (IdealSheafData.inclusion hJI)
  let e := (Etale.lowerStarComp AddCommGrpCat.{u + 1}
    (IdealSheafData.inclusion hJI) J.subschemeι I.subschemeι
    (IdealSheafData.inclusion_subschemeι hJI).symm).app I.subscheme.gmSheaf
  have : Epi (gmSheafToLowerStarGmSheaf J.subschemeι) :=
    epi_gmSheafToLowerStar_nilIdeal X J (hJI.trans hIN)
  obtain ⟨a⟩ := image_kernel_comp_iso
    (gmSheafToLowerStarGmSheaf J.subschemeι) (F.map r)
    (gmSheafToLowerStarGmSheaf I.subschemeι) e
    (gmSheafToLowerStar_comp (IdealSheafData.inclusion hJI) J.subschemeι I.subschemeι
      (IdealSheafData.inclusion_subschemeι hJI).symm)
  exact ⟨a ≪≫ (PreservesKernel.iso F r).symm⟩

end AlgebraicGeometry.Scheme
