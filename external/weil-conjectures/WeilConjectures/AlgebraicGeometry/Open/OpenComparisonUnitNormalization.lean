/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Unit normalization of the open etale/pro-etale comparison

## Main definitions

- `openComparisonRestrictionIso`: the canonical inverse-image comparison in restriction form.
- `openComparisonHomEquiv`: the displayed composite of four natural Hom bijections.

## Main statements

- `openComparison_unit_normalization`: the Hom formula and the open-unit equation.

## References

* Stacks Project, Tag 09AF, common-right-adjoint proof
* Stacks Project, Tags 099R and 09AF
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory

private lemma homEquiv_conjugate {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂)
    (F : C) (M : D) (h : L₁.obj F ⟶ M) :
    (b.homEquiv F M).symm (a.homEquiv F M h ≫ e.hom.app M) =
      ((conjugateIsoEquiv a b).symm e).hom.app F ≫ h := by
  apply (b.homEquiv F M).injective
  rw [Equiv.apply_symm_apply]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  change a.unit.app F ≫ R₁.map h ≫ e.hom.app M =
    b.unit.app F ≫ R₂.map (((conjugateEquiv a b).symm e.hom).app F) ≫ R₂.map h
  rw [← reassoc_of% (unit_conjugateEquiv_symm a b e.hom F), e.hom.naturality]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical pullback comparison, expressed using localization restriction on both
sites. The first factor converts etale restriction to inverse image; the middle factor
is the recorded canonical comparison, and the last converts pro-etale inverse image to
restriction. No independent comparison is chosen. -/
noncomputable def openComparisonRestrictionIso (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
      Functor.isoWhiskerLeft _
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)

/-- The displayed Hom chain of Tag 09AF: the comparison adjunction, the etale open
adjunction, postcomposition with the sectionwise identity `r R_X ≅ R_U s`, and the
inverses of the comparison and pro-etale open adjunctions. Every factor is a natural
bijection, so their composite is natural in the two sheaves. -/
noncomputable def openComparisonHomEquiv (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ⟶ M) ≃
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) ⟶ M) :=
  (((comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _).trans
    ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _)).trans
      (((comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).app M
        ).homToEquiv.trans
        (((comparisonAdjunction (ModuleCat.{u + 1} A) U).homEquiv _ _).symm.trans
          ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma openComparisonRestrictionIso_conjugate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
        (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j))
      ((Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) U))
      (openComparisonRestrictionIso A j).hom =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  let B := ModuleCat.{u + 1} A
  let r₀ := Etale.upperStarLowerStarAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s₀ := upperStarLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  change conjugateEquiv (cX.comp s) (r.comp cU)
    (Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j).inv _ ≫
      (supportSiteComparisonCoefficientPullbackIso B j).hom ≫
        Functor.whiskerLeft (comparisonUpperStar B X)
          (upperStarIsoOpenImmersionRestriction B j).hom) = _
  rw [← conjugateEquiv_comp (cX.comp s) (r₀.comp cU) (r.comp cU),
    ← conjugateEquiv_comp (cX.comp s) (cX.comp s₀) (r₀.comp cU),
    conjugateEquiv_whiskerLeft s s₀ cX
      (upperStarIsoOpenImmersionRestriction B j).hom,
    conjugateEquiv_whiskerRight r₀ r cU
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv]
  have he : conjugateEquiv r₀ r
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have hp : conjugateEquiv s s₀
      (upperStarIsoOpenImmersionRestriction B j).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [he, hp]
  change (𝟙 _ ≫ (conjugateEquiv (cX.comp s₀) (r₀.comp cU))
    (supportSiteComparisonCoefficientPullbackIso B j).hom) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  exact congrArg Iso.inv
    ((conjugateIsoEquiv (r₀.comp cU) (cX.comp s₀)).apply_symm_apply
      (supportSiteComparisonCoefficientDirectImageIso B j).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma openComparisonRestriction_directImage_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom)
      ) =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  ext M : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]
  change M.obj.map _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ M.obj.map _)) =
    𝟙 _ ≫ M.obj.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, Scheme.toProEt,
      supportSiteComparisonSiteBaseChangeIso]
  rfl

/-- The natural Hom chain sends `h` to `c_F⁻¹ ≫ h`, and the specified comparison `c`
intertwines the two open units via the canonical restriction comparison `a`. -/
theorem openComparison_unit_normalization (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (h : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ⟶ M),
      openComparisonHomEquiv A j F M h =
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j).inv.app F ≫
          h) ∧
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
          ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app F) ≫
        (openComparisonRestrictionIso A j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
          ((openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} A) j).hom.app F) =
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F)) := by
  constructor
  · intro F M h
    simpa [openComparisonHomEquiv, Adjunction.comp_homEquiv, Iso.homToEquiv,
      openImmersionLowerShriekComparisonUpperStarIso] using
      homEquiv_conjugate
        ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).comp
          (comparisonAdjunction (ModuleCat.{u + 1} A) X))
        ((comparisonAdjunction (ModuleCat.{u + 1} A) U).comp
          (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j))
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j) F M h
  · intro F
    let B := ModuleCat.{u + 1} A
    let cU := comparisonAdjunction B U
    let cX := comparisonAdjunction B X
    let e := Etale.openImmersionLowerShriekAdjunction B j
    let d := openImmersionLowerShriekAdjunction B j
    let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
    let s := openImmersionRestrictionLowerStarAdjunction B j
    let α := TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom
    let β := TwoSquare.mk _ _ _ _
      (openImmersionLowerShriekComparisonUpperStarIso B j).inv
    let θ := TwoSquare.mk _ _ _ _ (comparisonLowerStarOpenImmersionRestrictionIso B j).hom
    have ha : mateEquiv cX cU α = θ := by
      apply (mateEquiv s r).injective
      change (mateEquiv s r (mateEquiv cX cU α)) =
        (mateEquiv s r θ)
      rw [iterated_mateEquiv_conjugateEquiv]
      exact (openComparisonRestrictionIso_conjugate A j).trans
        (openComparisonRestriction_directImage_mate A j).symm
    have hb : mateEquiv cX cU (mateEquiv e d β) = θ := by
      rw [iterated_mateEquiv_conjugateEquiv]
      exact congrArg Iso.hom
        ((conjugateIsoEquiv (e.comp cX) (cU.comp d)).apply_symm_apply
          (comparisonLowerStarOpenImmersionRestrictionIso B j))
    have h : mateEquiv e d β = α := (mateEquiv cX cU).injective (hb.trans ha.symm)
    have hu := unit_mateEquiv e d β F
    rw [h] at hu
    change (comparisonUpperStar B U).map (e.unit.app F) ≫
      (openComparisonRestrictionIso A j).hom.app _ =
        d.unit.app _ ≫ (openImmersionRestriction B j).map
          ((openImmersionLowerShriekComparisonUpperStarIso B j).inv.app F) at hu
    rw [reassoc_of% hu, ← Functor.map_comp]
    simp
    rfl

end AlgebraicGeometry.ProEtale
