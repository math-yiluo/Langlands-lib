/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison

/-! # Ordinary scalar pullback compatibility

Source: Stacks Project, Tags 03EK, 0D6D and 07A6.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve shared functor expressions in the proof term.
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
open CategoryTheory
universe uA vA uB vB uC vC uD vD uE vE uF vF
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {F : Type uF} [Category.{vF} F]
section
variable {G : A ⥤ B} {T : B ⥤ C} {g : D ⥤ E} {t : E ⥤ F}
  {EA : A ⥤ D} {EB : B ⥤ E} {EC : C ⥤ F}
private def paste_iso (q₁ : G ⋙ EB ≅ EA ⋙ g) (q₃ : T ⋙ EC ≅ EB ⋙ t) :
    (G ⋙ T) ⋙ EC ≅ EA ⋙ (g ⋙ t) :=
  Functor.associator G T EC ≪≫ Functor.isoWhiskerLeft G q₃ ≪≫
    (Functor.associator G EB t).symm ≪≫ Functor.isoWhiskerRight q₁ t ≪≫
      Functor.associator EA g t

private theorem paste_iso_hom_app (q₁ : G ⋙ EB ≅ EA ⋙ g) (q₃ : T ⋙ EC ≅ EB ⋙ t)
    (M : A) :
    (paste_iso q₁ q₃).hom.app M = q₃.hom.app (G.obj M) ≫ t.map (q₁.hom.app M) := by
  simp [paste_iso]

private theorem paste_iso_inv_app (q₁ : G ⋙ EB ≅ EA ⋙ g) (q₃ : T ⋙ EC ≅ EB ⋙ t)
    (M : A) :
    (paste_iso q₁ q₃).inv.app M = t.map (q₁.inv.app M) ≫ q₃.inv.app (G.obj M) := by
  simp [paste_iso]
end

private theorem mate_of_unit
    {G : A ⥤ C} {H : B ⥤ D}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (q : L₁ ⋙ H ≅ G ⋙ L₂) (r : R₁ ⋙ G ⟶ H ⋙ R₂)
    (h : ∀ X, G.map (a₁.unit.app X) ≫ r.app (L₁.obj X) ≫ R₂.map (q.hom.app X) =
      a₂.unit.app (G.obj X)) :
    (mateEquiv a₁ a₂ q.inv) = r := by
  have he : q.inv = ((mateEquiv a₁ a₂).symm r) := by
    apply NatTrans.ext
    funext X
    apply (a₂.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    erw [← unit_mateEquiv_symm a₁ a₂ r X]
    apply (cancel_mono (R₂.map (q.hom.app X))).mp
    rw [Category.assoc, ← R₂.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    simpa only [Category.assoc] using (h X).symm
  rw [he]
  exact (mateEquiv a₁ a₂).apply_symm_apply r

private theorem paste_mate
    {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q₁ : L₁ ⋙ H ≅ G ⋙ L₂) (q₃ : L₃ ⋙ K ≅ H ⋙ L₄)
    (p₁ : R₁ ⋙ G ≅ H ⋙ R₂) (p₃ : R₃ ⋙ H ≅ K ⋙ R₄)
    (q : (L₁ ⋙ L₃) ⋙ K ≅ G ⋙ (L₂ ⋙ L₄))
    (p : (R₃ ⋙ R₁) ⋙ G ≅ K ⋙ (R₄ ⋙ R₂))
    (hq : ∀ X, q.inv.app X = L₄.map (q₁.inv.app X) ≫ q₃.inv.app (L₁.obj X))
    (hp : ∀ Z, p.hom.app Z = p₁.hom.app (R₃.obj Z) ≫ R₂.map (p₃.hom.app Z))
    (h₁ : (mateEquiv a₁ a₂ q₁.inv) = p₁.hom)
    (h₃ : (mateEquiv a₃ a₄ q₃.inv) = p₃.hom) :
    (mateEquiv (a₁.comp a₃) (a₂.comp a₄) q.inv) = p.hom := by
  have hv : TwoSquare.vComp q₁.inv q₃.inv = q.inv := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [TwoSquare.vComp, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    exact (hq X).symm
  have hh := mateEquiv_hcomp a₁ a₂ a₃ a₄ q₁.inv q₃.inv
  rw [hv] at hh
  change (mateEquiv (a₁.comp a₃) (a₂.comp a₄) q.inv) =
    TwoSquare.hComp (mateEquiv a₃ a₄ q₃.inv)
      (mateEquiv a₁ a₂ q₁.inv) at hh
  rw [h₁, h₃] at hh
  rw [hh]
  apply NatTrans.ext
  funext Z
  simp only [TwoSquare.hComp, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  exact (hp Z).symm

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct
open CategoryTheory.InternalAbelianSheafModule

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private theorem comapLowerStarIso_apply (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V) (M : Modules Λ' U) (W : V.ProEtᵒᵖ)
    (x : M.X.obj.obj ((InternalModuleOperations.siteMap h).op.obj W)) :
    ((CondensedRing.comapLowerStarIso φ h).hom.app M).hom.hom.app W x = x := by
  have he := Mod.comapMapModComapIso_hom_app_hom (h)_*[Ab.{u + 1}]
    (coefficientMap φ U) (coefficientMap φ V)
    (condensedPushforwardHom Λ h) (condensedPushforwardHom Λ' h)
    (condensedPushforwardHom_comp_map_coefficientMap φ h).symm M
  exact congrArg (fun t ↦ t.hom.app W x) he

private theorem pushComparison_apply
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules A X) (U : Y.ProEtᵒᵖ)
    (x : M.X.obj.obj ((InternalModuleOperations.siteMap f).op.obj U)) :
    ((ModuleRingedComparison.pushComparison A f).hom.app M).val.app U x = x := by
  change ((InternalModuleOperations.lowerComparison A f).hom.app M).val.app U x = x
  unfold InternalModuleOperations.lowerComparison
  exact (InternalModuleOperations.lowerComparison_existsUnique A f).exists.choose_spec M U x

private theorem generator_one (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (M : Modules Λ T) (U : T.ProEtᵒᵖ) (x : M.X.obj.obj U) :
    internalScalarGenerator (Scheme.ProEt.topology T) (coefficientMap a T) M U
        (1 : (ModuleRingedComparison.ring Λ' T).obj.obj U) x =
      (((Mod.extendRestrictAdjunction (coefficientMap a T)).unit.app M).hom.hom.app U) x := by
  let J := Scheme.ProEt.topology T
  let S := condensedRingObj Λ' T
  let φ := coefficientMap a T
  let one : S.obj.obj U := (1 : (ModuleRingedComparison.ring Λ' T).obj.obj U)
  have h := congrArg (fun f ↦ f.hom.app U) (Mod.whiskerLeft_extendUnitHom_smul' φ M)
  have hμ := congr_app (Functor.LaxMonoidal.μ_natural_right
    (sheafToPresheaf J AddCommGrpCat.{u + 1}) S (Mod.extendUnitHom φ M)) U
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f ≫ (Mod.act ((Mod.extendScalars φ).obj M).X).hom.app U) hμ)
      (one ⊗ₜ[ℤ] x)
  change internalScalarGenerator J φ M U (1 : (ModuleRingedComparison.ring Λ' T).obj.obj U) x = _
  change
    (((sheafToPresheaf J AddCommGrpCat.{u + 1}).obj S ◁
      (sheafToPresheaf J AddCommGrpCat.{u + 1}).map (Mod.extendUnitHom φ M)).app U ≫
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1}) S
        (Mod.extendScalarsObj φ M).X).app U) ≫
      (Mod.act (Mod.extendScalarsObj φ M).X).hom.app U) (one ⊗ₜ[ℤ] x) =
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1}) S M.X).app U) ≫
      (S ◁ Mod.extendUnitHom φ M ≫ (Mod.act (Mod.extendScalarsObj φ M).X)).hom.app U)
        (one ⊗ₜ[ℤ] x) at hh
  rw [h] at hh
  have hsmul : internalScalarGenerator J φ M U one x =
      (1 : (ModuleRingedComparison.ring Λ' T).obj.obj U) •
        (show ((ModuleRingedComparison.equivalence Λ' T).functor.obj
          ((extension a T).obj M)).val.obj U from
          (((Mod.extendRestrictAdjunction φ).unit.app M).hom.hom.app U x)) := hh.symm
  simpa only [one_smul] using hsmul

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

-- Compare the scalar unit and its inverse mate through the specified section equivalence.
private theorem scalar_mate (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (hs : SectionScalarNormalized a T s) :
    (mateEquiv (Mod.extendRestrictAdjunction (coefficientMap a T))
      s.pair.ordinaryAdjunction s.ordinary.inv) = s.restriction.hom := by
  let ER := (ModuleRingedComparison.equivalence Λ T).functor
  let φ := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T)
  have hu (M : Modules Λ T) (U : T.ProEtᵒᵖ) (x : M.X.obj.obj U) :
      (s.ordinary.hom.app M).val.app U
          ((((Mod.extendRestrictAdjunction (coefficientMap a T)).unit.app M).hom.hom.app U) x) =
        (s.pair.ordinaryAdjunction.unit.app (ER.obj M)).val.app U x := by
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ U).map
        (eqToHom (s.pair.extension_obj (ER.obj M))))).injective
    have hgen := hs.2.1 M U (1 : (ModuleRingedComparison.ring Λ' T).obj.obj U) x
    rw [generator_one] at hgen
    exact hgen.trans (s.pair.ordinaryUnit (ER.obj M) U x).symm
  have hunit (M : Modules Λ T) :
      ER.map ((Mod.extendRestrictAdjunction (coefficientMap a T)).unit.app M) ≫
        s.restriction.hom.app ((extension a T).obj M) ≫
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} φ).map (s.ordinary.hom.app M) =
      s.pair.ordinaryAdjunction.unit.app (ER.obj M) := by
    ext U x
    change (s.ordinary.hom.app M).val.app U
      ((s.restriction.hom.app ((extension a T).obj M)).val.app U
        (((Mod.extendRestrictAdjunction (coefficientMap a T)).unit.app M).hom.hom.app U x)) = _
    rw [hs.1]
    exact hu M U x
  exact mate_of_unit (Mod.extendRestrictAdjunction (coefficientMap a T))
    s.pair.ordinaryAdjunction s.ordinary s.restriction.hom hunit

-- Compare the specified composite adjunctions and all four section functors explicitly.
/-- The ordinary scalar and geometric comparisons preserve the balanced pullback square.
Source: Stacks Project, Tags 03EK, 0D6D and 07A6.
(auxiliary; not a blueprint node)

Proof: the scalar generator equations identify the specified scalar adjunctions:
the units send m to 1 tensor m. This identifies each inverse mate with the
specified restriction comparison.
Paste these two adjunction squares with the geometric adjunction squares.
The resulting right-adjoint rectangle is the identity on sections, by the scalar
restriction normalizations, the geometric pushforward comparisons, coefficient
compatibility and the hypothesis on r. It is thus r. Both left-adjoint rectangles
have that same conjugate; injectivity of conjugateEquiv identifies them. Evaluate
this equality at M. The internal left rectangle is CondensedRing.pullIso inverse
by its definition as the conjugate of comapLowerStarIso. This gives the equation.
The argument uses no flatness or nonzero-coefficient assumption. -/
theorem section_ordinary_pull_compatibility (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y)
    (hX : SectionScalarNormalized a X sX) (hY : SectionScalarNormalized a Y sY)
    (r : ModuleRingedComparison.pushforward Λ' f ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) (coefficientMap a Y)) ≅
        SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward Λ f)
    (identity_on_sections : (∀ (N : ModuleRingedComparison.modules Λ' X) (U : Y.ProEtᵒᵖ)
      (x : ((ModuleRingedComparison.pushforward Λ' f).obj N).val.obj U),
    (r.hom.app N).val.app U x = x))
    (c : sY.pair.extension ⋙ ModuleRingedComparison.pullback Λ' f ≅
    ModuleRingedComparison.pullback Λ f ⋙ sX.pair.extension)
    (conjugate : conjugateEquiv
      (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
      ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction) c.inv = r.hom)
 :
    ∀ M : Modules Λ Y,
    (ModuleRingedComparison.equivalence Λ' X).functor.map
        ((CondensedRing.pullIso a f).inv.app M) ≫
        sX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
        sX.pair.extension.map ((ModuleRingedComparison.pullComparison Λ f).hom.app M) =
      (ModuleRingedComparison.pullComparison Λ' f).hom.app ((extension a Y).obj M) ≫
        (ModuleRingedComparison.pullback Λ' f).map (sY.ordinary.hom.app M) ≫
        c.hom.app ((ModuleRingedComparison.equivalence Λ Y).functor.obj M) := by
  let q := ModuleRingedComparison.pullComparison Λ f
  let q' := ModuleRingedComparison.pullComparison Λ' f
  let p := ModuleRingedComparison.pushComparison Λ f
  let p' := ModuleRingedComparison.pushComparison Λ' f
  let q02 : (CondensedRing.upperStar Λ f ⋙ extension a X) ⋙
      (ModuleRingedComparison.equivalence Λ' X).functor ≅
      (ModuleRingedComparison.equivalence Λ Y).functor ⋙
        (ModuleRingedComparison.pullback Λ f ⋙ sX.pair.extension) :=
    paste_iso q sX.ordinary
  let p02 : (V₀ a X ⋙ CondensedRing.lowerStar Λ f) ⋙
      (ModuleRingedComparison.equivalence Λ Y).functor ≅
      (ModuleRingedComparison.equivalence Λ' X).functor ⋙
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
            ModuleRingedComparison.pushforward Λ f) :=
    paste_iso sX.restriction p
  have hq : (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f)
      (ModuleRingedComparison.adjunction Λ f) q.inv) = p.hom :=
    (InternalModuleOperations.upperComparison_existsUnique Λ f).exists.choose_spec
  have hq' : (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ' f)
      (ModuleRingedComparison.adjunction Λ' f) q'.inv) = p'.hom :=
    (InternalModuleOperations.upperComparison_existsUnique Λ' f).exists.choose_spec
  have h02 : (mateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (Mod.extendRestrictAdjunction (coefficientMap a X)))
      ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction)
      q02.inv) = p02.hom := by
    apply paste_mate (CondensedRing.upperStarLowerStarAdjunction Λ f)
      (ModuleRingedComparison.adjunction Λ f)
      (Mod.extendRestrictAdjunction (coefficientMap a X)) sX.pair.ordinaryAdjunction
      q sX.ordinary p sX.restriction q02 p02
    · intro M
      simp only [q02, paste_iso_inv_app]
    · intro N
      simp only [p02, paste_iso_hom_app]
    · exact hq
    · exact scalar_mate a X sX hX
  have hi : conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (Mod.extendRestrictAdjunction (coefficientMap a X)))
      ((Mod.extendRestrictAdjunction (coefficientMap a Y)).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ' f))
      (CondensedRing.pullIso a f).inv = (CondensedRing.comapLowerStarIso a f).inv := by
    exact congrArg Iso.inv ((conjugateIsoEquiv
      ((Mod.extendRestrictAdjunction (coefficientMap a Y)).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ' f))
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (Mod.extendRestrictAdjunction (coefficientMap a X)))).apply_symm_apply
          (CondensedRing.comapLowerStarIso a f))
  have hc : conjugateEquiv
      ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction)
      (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
      c.hom = r.inv := by
    let hh := (conjugateIsoEquiv
      (sY.pair.ordinaryAdjunction.comp (ModuleRingedComparison.adjunction Λ' f))
      ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction)) c.symm
    have he : hh = r := by
      apply Iso.ext
      simpa only [hh, conjugateIsoEquiv_apply_hom, Iso.symm_hom] using conjugate
    simpa only [hh, conjugateIsoEquiv_apply_inv, Iso.symm_inv] using congrArg Iso.inv he
  have hr : ∀ N : Modules Λ' X,
      sY.restriction.hom.app ((CondensedRing.lowerStar Λ' f).obj N) ≫
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) (coefficientMap a Y))).map
            (p'.hom.app N) ≫ r.hom.app ((ModuleRingedComparison.equivalence Λ' X).functor.obj N) =
      (ModuleRingedComparison.equivalence Λ Y).functor.map
        ((CondensedRing.comapLowerStarIso a f).hom.app N) ≫ p02.hom.app N := by
    intro N
    ext U x
    simp only [p02, paste_iso_hom_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    change (r.hom.app ((ModuleRingedComparison.equivalence Λ' X).functor.obj N)).val.app U
        ((p'.hom.app N).val.app U
          ((sY.restriction.hom.app ((CondensedRing.lowerStar Λ' f).obj N)).val.app U x)) =
      (sX.restriction.hom.app N).val.app
        ((InternalModuleOperations.siteMap f).op.obj U)
        ((p.hom.app ((V₀ a X).obj N)).val.app U
          (((CondensedRing.comapLowerStarIso a f).hom.app N).hom.hom.app U x))
    have hl := (identity_on_sections
      ((ModuleRingedComparison.equivalence Λ' X).functor.obj N) U
      ((p'.hom.app N).val.app U
        ((sY.restriction.hom.app ((CondensedRing.lowerStar Λ' f).obj N)).val.app U x))).trans
      ((congrArg ((p'.hom.app N).val.app U)
        (hY.1 ((CondensedRing.lowerStar Λ' f).obj N) U x)).trans
          (pushComparison_apply Λ' f N U x))
    have hr := (hX.1 N ((InternalModuleOperations.siteMap f).op.obj U)
      ((p.hom.app ((V₀ a X).obj N)).val.app U
        (((CondensedRing.comapLowerStarIso a f).hom.app N).hom.hom.app U x))).trans
      ((pushComparison_apply Λ f ((V₀ a X).obj N) U
        (((CondensedRing.comapLowerStarIso a f).hom.app N).hom.hom.app U x)).trans
          (comapLowerStarIso_apply a f N U x))
    exact hl.trans hr.symm
  have hh := equivalenceAdjunctionComparison_compositor
    (ModuleRingedComparison.equivalence Λ Y) (ModuleRingedComparison.equivalence Λ' Y)
    (ModuleRingedComparison.equivalence Λ' X)
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (CondensedRing.upperStarLowerStarAdjunction Λ' f)
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
      (Mod.extendRestrictAdjunction (coefficientMap a X)))
    sY.pair.ordinaryAdjunction (ModuleRingedComparison.adjunction Λ' f)
    ((ModuleRingedComparison.adjunction Λ f).comp sX.pair.ordinaryAdjunction)
    sY.restriction p' p02 sY.ordinary q' q02
    (scalar_mate a Y sY hY) hq' h02 (CondensedRing.comapLowerStarIso a f) r hr
    (CondensedRing.pullIso a f).symm c hi hc
  intro M
  simpa only [q02, paste_iso_hom_app, Category.assoc, q, q', Iso.symm_hom,
    Functor.comp_obj] using hh M

end AlgebraicGeometry.ProEtale.QuotientChange
