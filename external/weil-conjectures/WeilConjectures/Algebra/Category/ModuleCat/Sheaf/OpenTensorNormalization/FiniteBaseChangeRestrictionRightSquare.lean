/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.AlgebraicGeometry.FixedScalarOpenSquareSectionMate

/-! Right-adjoint ordinary square for the finite restriction construction.
(blueprint: new-lem-sf-finite-base-change-restriction-right-square)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem sectionwise_hom_ext {U : Scheme.{u}}
    {R : Sheaf (ProEt.topology U) RingCat.{u + 1}}
    {P Q : SheafOfModules.{u + 1} R} {f g : P ⟶ Q}
    (h : ∀ (W : U.ProEtᵒᵖ) (x : P.val.obj W), f.val.app W x = g.val.app W x) :
    f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  exact h W x

private theorem realization_map_sections {A : Type (u + 1)} [CommRing A]
    {U : Scheme.{u}} {R : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    {i : (Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A U R i) {M N : FiniteModules A U} (f : M ⟶ N)
    (W : U.ProEtᵒᵖ) (x : (e.equivalence.functor.obj M).val.obj W) :
    (e.underlying.hom.app N).hom.app W ((e.equivalence.functor.map f).val.app W x) =
      f.hom.app W ((e.underlying.hom.app M).hom.app W x) :=
  ConcreteCategory.congr_hom (congr_app
    (congrArg (sheafToPresheaf (ProEt.topology U) AddCommGrpCat.{u + 1}).map
      (e.underlying.hom.naturality f)) W) x

private theorem realization_restrict_sections {A : Type (u + 1)} [CommRing A]
    {U : Scheme.{u}} {R : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    {i : (Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A U R i) (M : FiniteModules A U)
    {W V : U.ProEtᵒᵖ} (f : W ⟶ V) (x : (e.equivalence.functor.obj M).val.obj W) :
    (e.underlying.hom.app M).hom.app V ((e.equivalence.functor.obj M).val.map f x) =
      M.obj.map f ((e.underlying.hom.app M).hom.app W x) :=
  ConcreteCategory.congr_hom ((e.underlying.hom.app M).hom.naturality f) x

private theorem realization_sections_injective {A : Type (u + 1)} [CommRing A]
    {U : Scheme.{u}} {R : Sheaf (ProEt.topology U) CommRingCat.{u + 1}}
    {i : (Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A U R i) (M : FiniteModules A U) (W : U.ProEtᵒᵖ) :
    Function.Injective ((e.underlying.hom.app M).hom.app W) :=
  (ConcreteCategory.bijective_of_isIso ((e.underlying.hom.app M).hom.app W)).injective

-- Explicit types keep the kernel from expanding the canonical adjunction data.
private def restrictionRightSquareMate
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (w : gU ≫ j = j' ≫ g) :
    ProEtale.lowerStar (ModuleCat.{u + 1} A) g ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} A) j ⟶
      ProEtale.upperStar (ModuleCat.{u + 1} A) j' ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} A) gU :=
  (mateEquiv
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU)
    (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) w).hom)

private theorem restrictionRightSquareMate_cancel
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : gU ≫ j = j' ≫ g) :
    Functor.whiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} A) g)
        (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom ≫
      ProEtale.fixedScalarOpenSquareRestrictionMate A gU j' j g w =
    restrictionRightSquareMate A gU j' j g w ≫
      Functor.whiskerRight
        (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j').hom
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) gU) := by
  exact Iso.hom_inv_id_assoc
    (Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} A) g)
      (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)) _

-- Use ordinary site objects so all evaluations have exactly the form `op W`.
private theorem restrictionRightSquare_mateSections
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (c : MorphismProperty.Over.pullback @WeaklyEtale ⊤ gU ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j') ⟶
      MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j) ⋙
        MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
    (hc : c = @ProEtale.fixedScalarOpenSquareSectionComparison U' U X' X gU j' j g
      sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w)
    (α : ProEtale.upperStar (ModuleCat.{u + 1} A) j ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j)
    (hα : α = ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)
    (α' : ProEtale.upperStar (ModuleCat.{u + 1} A) j' ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j')
    (hα' : α' = ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j')
    (δ : ProEtale.lowerStar (ModuleCat.{u + 1} A) g ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} A) j ⟶
      ProEtale.upperStar (ModuleCat.{u + 1} A) j' ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} A) gU)
    (hδ : δ = restrictionRightSquareMate A gU j' j g sq.toCommSq.w) :
    ∀ (M : FiniteModules A X') (W : U.ProEt)
      (y : ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M)).obj.obj (op W)),
      M.obj.map (c.app W).op
          ((α.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M)).hom.app (op W) y) =
        (α'.hom.app M).hom.app ((baseChange .ordinary gU).op.obj (op W))
          ((δ.app M).hom.app (op W) y) := by
  subst c
  intro M
  let gM := (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M
  have hcancel :
      Functor.whiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} A) g) α.hom ≫
          (@ProEtale.fixedScalarOpenSquareRestrictionMate A _ U' U X' X gU j' j g
            sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w) =
        δ ≫ Functor.whiskerRight α'.hom (ProEtale.lowerStar (ModuleCat.{u + 1} A) gU) := by
    simpa only [hδ, hα, hα'] using
      (restrictionRightSquareMate_cancel A gU j' j g sq.toCommSq.w)
  intro W y
  have hM := congr_app hcancel M
  have hW := congr_app (congrArg (fun f ↦ f.hom) hM) (op W)
  change (α.hom.app gM).hom.app (op W) ≫
      ((@ProEtale.fixedScalarOpenSquareRestrictionMate A _ U' U X' X gU j' j g
        sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w).app M).hom.app (op W) =
    (δ.app M).hom.app (op W) ≫
      (((ProEtale.lowerStar (ModuleCat.{u + 1} A) gU).map (α'.hom.app M)).hom.app (op W))
    at hW
  rw [ProEtale.fixed_scalar_open_square_section_mate A gU j' j g sq M W,
    ProEtale.lowerStar_map_hom_app] at hW
  exact ConcreteCategory.congr_hom hW y

-- Allow the complete section calculation to elaborate in one theorem.
private theorem restrictionRightSquare_fromMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (α : ProEtale.upperStar (ModuleCat.{u + 1} A) j ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j)
    (hα : α = ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)
    (α' : ProEtale.upperStar (ModuleCat.{u + 1} A) j' ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j')
    (hα' : α' = ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j')
    (δ : ProEtale.lowerStar (ModuleCat.{u + 1} A) g ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} A) j ⟶
      ProEtale.upperStar (ModuleCat.{u + 1} A) j' ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} A) gU)
    (hδ : δ = restrictionRightSquareMate A gU j' j g sq.toCommSq.w) :
    ∀ M : FiniteModules A X',
      e.open_pin.star.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M) ≫
        (restrict .ordinary j (finiteInput A gU j' j g sq).R).map
          (e.pull_pin.right.hom.app M) ≫
        o.rightSquare.hom.app (e.realizeX'.equivalence.functor.obj M) =
      e.realizeU.equivalence.functor.map
          (δ.app M) ≫
        e.pullU_pin.right.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j').obj M) ≫
        (direct .ordinary gU _ _ (cornerCoefficient t)).map
          (e.open'_pin.star.hom.app M) := by
  intro M
  have hc (W : U.ProEt) : t.iso.inv.app W =
      (@ProEtale.fixedScalarOpenSquareSectionComparison U' U X' X gU j' j g
        sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w).app W := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact (eq_of_heq (t.first W)).trans (by
        simp [ProEtale.fixedScalarOpenSquareSectionComparison,
          MorphismProperty.Over.pullbackMapComparison, baseFirst, openInclusion,
          proEtaleOpenComposition, baseChange])
    · exact (MorphismProperty.Over.w (t.iso.inv.app W)).trans (by
        simp [ProEtale.fixedScalarOpenSquareSectionComparison,
          MorphismProperty.Over.pullbackMapComparison, openInclusion,
          proEtaleOpenComposition, baseChange])
  let gM := (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M
  let jgM := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj gM
  let jM := (ProEtale.upperStar (ModuleCat.{u + 1} A) j').obj M
  have hc' : t.iso.inv =
      @ProEtale.fixedScalarOpenSquareSectionComparison U' U X' X gU j' j g
        sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w := by
    ext W
    exact hc W
  have hm := restrictionRightSquare_mateSections A gU j' j g sq t.iso.inv hc'
    α hα α' hα' δ hδ M
  apply sectionwise_hom_ext
  intro W x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  apply realization_sections_injective e.realizeX' M
    ((openInclusion .ordinary j').op.obj ((baseChange .ordinary gU).op.obj W))
  change (e.realizeX'.underlying.hom.app M).hom.app
      ((openInclusion .ordinary j').op.obj ((baseChange .ordinary gU).op.obj W))
      ((o.rightSquare.hom.app (e.realizeX'.equivalence.functor.obj M)).val.app W
        ((e.pull_pin.right.hom.app M).val.app ((openInclusion .ordinary j).op.obj W)
          ((e.open_pin.star.hom.app gM).val.app W x))) =
    (e.realizeX'.underlying.hom.app M).hom.app
      ((openInclusion .ordinary j').op.obj ((baseChange .ordinary gU).op.obj W))
      ((e.open'_pin.star.hom.app M).val.app ((baseChange .ordinary gU).op.obj W)
        ((e.pullU_pin.right.hom.app jM).val.app W
          ((e.realizeU.equivalence.functor.map (δ.app M)).val.app W x)))
  have hs := by
    exact congrArg
      (fun y ↦ (e.realizeX'.underlying.hom.app M).hom.app
        ((openInclusion .ordinary j').op.obj ((baseChange .ordinary gU).op.obj W)) y)
      (o.rightSections (e.realizeX'.equivalence.functor.obj M) W
        ((e.pull_pin.right.hom.app M).val.app ((openInclusion .ordinary j).op.obj W)
          ((e.open_pin.star.hom.app gM).val.app W x)))
  have hnx := by
    exact realization_map_sections e.realizeU (δ.app M) W x
  have hn'x := by
    exact realization_restrict_sections e.realizeX' M
      (t.iso.inv.app W.unop).op
      ((e.pull_pin.right.hom.app M).val.app ((openInclusion .ordinary j).op.obj W)
        ((e.open_pin.star.hom.app gM).val.app W x))
  have hl₁ := by
    exact congrArg (fun y ↦ M.obj.map (t.iso.inv.app W.unop).op y)
      (e.pull_pin.right_sections M ((openInclusion .ordinary j).op.obj W)
        ((e.open_pin.star.hom.app gM).val.app W x))
  have hl₂ := by
    exact congrArg (fun y ↦ M.obj.map (t.iso.inv.app W.unop).op y)
      (e.open_pin.sections gM W x)
  rw [← hα] at hl₂
  have hr₁ := by
    exact e.open'_pin.sections M ((baseChange .ordinary gU).op.obj W)
      ((e.pullU_pin.right.hom.app jM).val.app W
        ((e.realizeU.equivalence.functor.map (δ.app M)).val.app W x))
  rw [← hα'] at hr₁
  have hr₂ := by
    exact congrArg
      (fun y ↦ (α'.hom.app M).hom.app ((baseChange .ordinary gU).op.obj W) y)
      (e.pullU_pin.right_sections jM W
        ((e.realizeU.equivalence.functor.map (δ.app M)).val.app W x))
  have hr₃ := by
    exact congrArg
      (fun y ↦ (α'.hom.app M).hom.app ((baseChange .ordinary gU).op.obj W) y) hnx
  have hmx := by
    exact hm W.unop ((e.realizeU.underlying.hom.app jgM).hom.app W x)
  have hl := by
    exact hs.trans hn'x
  have hl := by
    exact hl.trans hl₁
  have hl := by
    exact hl.trans hl₂
  have hr := by
    exact hr₁.trans hr₂
  have hr := by
    exact hr.trans hr₃
  have hl := by
    exact hl.trans hmx
  exact hl.trans hr.symm

/-- The right-adjoint square needed before mate transport.
Source: the finite ordinary pin-square calculation underlying the blueprint
coherence of evaluation, units, and counits. The proof identifies the site-square
inverse by pullback hom extensionality and evaluates the four pin sections; the
fixed-scalar section-mate closes the remaining equality. This is
strictly smaller than the parent because it contains no mate transport.
(blueprint: new-lem-sf-finite-base-change-restriction-right-square)
-/
theorem finite_base_change_restriction_right_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) :
    ∀ M : FiniteModules A X',
      e.open_pin.star.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M) ≫
        (restrict .ordinary j (finiteInput A gU j' j g sq).R).map
          (e.pull_pin.right.hom.app M) ≫
        o.rightSquare.hom.app (e.realizeX'.equivalence.functor.obj M) =
      e.realizeU.equivalence.functor.map
          ((mateEquiv
            (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
            (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU)
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom).app M) ≫
        e.pullU_pin.right.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j').obj M) ≫
        (direct .ordinary gU _ _ (cornerCoefficient t)).map
          (e.open'_pin.star.hom.app M) := by
  exact restrictionRightSquare_fromMate A gU j' j g sq o e
    (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j) rfl
    (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j') rfl
    (restrictionRightSquareMate A gU j' j g sq.toCommSq.w) rfl

end SheafOfModules.OpenTensorNormalization
