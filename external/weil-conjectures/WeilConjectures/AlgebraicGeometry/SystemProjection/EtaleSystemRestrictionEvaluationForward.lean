/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf

/-! # Forward restriction evaluation cube for ordinary systems

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks Tag 0GL6.

This is the forward cube whose cancellation gives the inverse restriction
comparison in `EtaleSystemRestrictionEvaluation`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

open WeilConjectures.SemilinearSections

private def constantRestriction (W : Scheme.{u})
    (A B : CommRingCat.{u + 1}) (a : A ⟶ B) :
    res ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map a) ⋙
      constantModule W A ≅ constantModule W B ⋙
        Sheaf.restrictScalars W.smallEtaleTopology a.hom := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun b ↦ ?_)) ?_)) ?_
  · ext x
    have hn := congrArg (fun g ↦ g.app U b)
      (toSheafify_naturality W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).map a))
    exact congrArg (fun c ↦ c • (show M.val.obj U from x)) hn
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private def ordinaryScalarEvaluation (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) (n : ℕ) :
    res (ringMap W a) ⋙ level W B n ≅ level W C n ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (a.app (op n)).hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (restrictionEvaluation_existsUnique W.smallEtaleTopology
        (coefficients W B) (transitions W B) (coefficients W C) (transitions W C)
        (fun n ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
          (a.app (op n))) (fun n ↦ by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun h ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map h)
            (a.naturality (homOfLE (Nat.le_succ n)).op).symm) n).exists.choose
      (constantModule W (B.obj (op n))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (constantRestriction W _ _ (a.app (op n))) ≪≫
    (Functor.associator _ _ _).symm

-- Reduce the identity maps through the sequence-site evaluation and constant-ring models.
attribute [local irreducible] eqToHom in
private theorem ordinaryScalarEvaluation_sections (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) (n : ℕ)
    (M : Modules W C) (U : W.Etaleᵒᵖ)
    (x : ((level W B n).obj ((res (ringMap W a)).obj M)).obj.obj U) :
    HEq (((ordinaryScalarEvaluation W a n).hom.app M).hom.app U x) x := by
  dsimp only [ordinaryScalarEvaluation, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]
  have hs := (restrictionEvaluation_existsUnique W.smallEtaleTopology
    (coefficients W B) (transitions W B) (coefficients W C) (transitions W C)
    (fun n ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
      (a.app (op n))) (fun n ↦ by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg
        (fun h ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map h)
        (a.naturality (homOfLE (Nat.le_succ n)).op).symm) n).exists.choose_spec M U
  have hs' := eq_of_heq hs
  have hx := congrArg (fun q ↦ q x) hs'
  exact heq_of_eq hx

private theorem mateCubeReflects
    {A B C D E F G H : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E} {L₄ : G ⥤ H} {R₄ : H ⥤ G}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {g : A ⥤ C} {h : B ⥤ D} {g' : E ⥤ G} {h' : F ⥤ H}
    {v : A ⥤ E} {w : B ⥤ F} {v' : C ⥤ G} {w' : D ⥤ H}
    (s : TwoSquare g L₁ L₂ h) (s' : TwoSquare g' L₃ L₄ h')
    (c : TwoSquare v L₁ L₃ w) (c' : TwoSquare v' L₂ L₄ w')
    (e : v ⋙ g' ≅ g ⋙ v') (d : w ⋙ h' ≅ h ⋙ w')
    (hc : ∀ N : B,
      g'.map ((mateEquiv a₁ a₃ c).app N) ≫
          (mateEquiv a₃ a₄ s').app (w.obj N) ≫ R₄.map (d.hom.app N) =
        e.hom.app (R₁.obj N) ≫ v'.map ((mateEquiv a₁ a₂ s).app N) ≫
          (mateEquiv a₂ a₄ c').app (h.obj N)) :
    ∀ M : A, L₄.map (e.hom.app M) ≫ c'.app (g.obj M) ≫ w'.map (s.app M) =
      s'.app (v.obj M) ≫ h'.map (c.app M) ≫ d.hom.app (L₁.obj M) := by
  have ht : Functor.whiskerRight e.hom L₄ ≫ (TwoSquare.hComp s c') =
      (TwoSquare.hComp c s') ≫ Functor.whiskerLeft L₁ d.hom := by
    apply (mateEquiv a₁ a₄).injective
    rw [mateEquiv_whiskerRight_comp, mateEquiv_comp_whiskerLeft,
      mateEquiv_vcomp a₁ a₂ a₄, mateEquiv_vcomp a₁ a₃ a₄]
    apply NatTrans.ext
    funext N
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      TwoSquare.vComp, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using (hc N).symm
  intro M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    TwoSquare.hComp, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app ht M

private theorem mateFromUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {G : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G L L' H) (β : TwoSquare R H G R')
    (hu : ∀ M, G.map (a.unit.app M) ≫ β.app (L.obj M) =
      b.unit.app (G.obj M) ≫ R'.map (α.app M)) : mateEquiv a b α = β := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (hu M).symm.trans (unit_mateEquiv_symm a b β M)

private theorem openRestrictionMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _ (Iso.refl
        (Sheaf.restrictScalars Z.smallEtaleTopology a ⋙
          openImmersionRestriction (ModuleCat.{u + 1} A) j)).hom)) =
      (lowerStarRestrictScalarsIso a j).hom := by
  apply mateFromUnit
  intro M
  calc
    _ = (Sheaf.restrictScalars Z.smallEtaleTopology a).map
        ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j).unit.app M) :=
      Category.comp_id _
    _ = (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((Sheaf.restrictScalars Z.smallEtaleTopology a).obj M) :=
      restrictScalars_map_openImmersionRestrictionLowerStarAdjunction_unit_app a j M
    _ = _ := by
      exact ((congrArg
        (fun q ↦ (openImmersionRestrictionLowerStarAdjunction
          (ModuleCat.{u + 1} A) j).unit.app
            ((Sheaf.restrictScalars Z.smallEtaleTopology a).obj M) ≫ q)
        ((lowerStar (ModuleCat.{u + 1} A) j).map_id _)).trans
          (Category.comp_id _)).symm

private theorem openExtensionMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _ (openImmersionLowerShriekRestrictScalarsIso a j).hom)) =
      (Iso.refl (openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars X.smallEtaleTopology a)).hom := by
  apply mateFromUnit
  intro M
  exact (Category.comp_id _).trans
    (openImmersionLowerShriekAdjunction_unit_app_comp_openImmersionRestrictionMap a j M).symm

-- Reduce the section groups through the actual sequence-site and constant-ring models.
attribute [local irreducible] eqToHom in
private theorem ordinaryInverseCube
    {X Y : Scheme.{u}} {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {g : X ⟶ Y} (a : B ⟶ C) (d : Image g B) (e : Image g C)
    (r : RestrictionImage a d e) (n : ℕ)
    (xb : Evaluation X B n) (xc : Evaluation X C n)
    (yb : Evaluation Y B n) (yc : Evaluation Y C n)
    (LB : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))))
    (LC : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (C.obj (op n))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (C.obj (op n))))
    [LB.Additive] [PreservesFiniteLimits LB] [PreservesFiniteColimits LB]
    [LC.Additive] [PreservesFiniteLimits LC] [PreservesFiniteColimits LC]
    (ab : LB ⊣ lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g)
    (ac : LC ⊣ lowerStar (ModuleCat.{u + 1} (C.obj (op n))) g)
    (eb : ImageEvaluation d n xb yb LB ab)
    (ec : ImageEvaluation e n xc yc LC ac)
    (sx : res (ringMap X a) ⋙ level X B n ≅ level X C n ⋙
      Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom)
    (sy : res (ringMap Y a) ⋙ level Y B n ≅ level Y C n ⋙
      Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom)
    (hsx : ∀ (M : Modules X C) (U : X.Etaleᵒᵖ)
      (x : ((level X B n).obj ((res (ringMap X a)).obj M)).obj.obj U),
      HEq (((sx.hom.app M).hom.app U) x) x)
    (hsy : ∀ (M : Modules Y C) (U : Y.Etaleᵒᵖ)
      (x : ((level Y B n).obj ((res (ringMap Y a)).obj M)).obj.obj U),
      HEq (((sy.hom.app M).hom.app U) x) x)
    (z : Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom ⋙ LB ≅
      LC ⋙ Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom)
    (hz : (mateEquiv ac ab (TwoSquare.mk _ _ _ _ z.hom)) =
      (lowerStarRestrictScalarsIso (a.app (op n)).hom g).hom) :
    ∀ M : Modules Y C,
      LB.map (sy.inv.app M) ≫ eb.inverse.hom.app ((res (ringMap Y a)).obj M) ≫
          (level X B n).map (r.inverseImage.hom.app M) =
        z.hom.app ((level Y C n).obj M) ≫
          (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
            (ec.inverse.hom.app M) ≫ sx.inv.app (e.inverse.obj M) := by
  apply mateCubeReflects e.adjunction d.adjunction ac ab
    (TwoSquare.mk _ _ _ _ r.inverseImage.hom)
    (TwoSquare.mk _ _ _ _ z.hom)
    (TwoSquare.mk _ _ _ _ ec.inverse.hom)
    (TwoSquare.mk _ _ _ _ eb.inverse.hom) sy.symm sx.symm
  have hr : (mateEquiv e.adjunction d.adjunction
      (TwoSquare.mk _ _ _ _ r.inverseImage.hom)) = r.ordinary.inv := by
    rw [r.inverseImage_mate]
    exact ((mateEquiv e.adjunction d.adjunction).apply_symm_apply _)
  have hb : (mateEquiv d.adjunction ab
      (TwoSquare.mk _ _ _ _ eb.inverse.hom)) = eb.ordinary.hom := by
    rw [eb.inverse_mate]
    exact ((mateEquiv d.adjunction ab).apply_symm_apply _)
  have hc : (mateEquiv e.adjunction ac
      (TwoSquare.mk _ _ _ _ ec.inverse.hom)) = ec.ordinary.hom := by
    rw [ec.inverse_mate]
    exact ((mateEquiv e.adjunction ac).apply_symm_apply _)
  have hxi (M : Modules X C) (U : X.Etaleᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
      HEq ((sx.inv.app M).hom.app U x) x := by
    have h := hsx M U ((sx.inv.app M).hom.app U x)
    have he := congrArg (fun f ↦ f.hom.app U) (sx.inv_hom_id_app M)
    have hv := ConcreteCategory.congr_hom he x
    change (sx.hom.app M).hom.app U ((sx.inv.app M).hom.app U x) = x at hv
    exact h.symm.trans (heq_of_eq hv)
  have hyi (M : Modules Y C) (U : Y.Etaleᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
      HEq ((sy.inv.app M).hom.app U x) x := by
    have h := hsy M U ((sy.inv.app M).hom.app U x)
    have he := congrArg (fun f ↦ f.hom.app U) (sy.inv_hom_id_app M)
    have hv := ConcreteCategory.congr_hom he x
    change (sy.hom.app M).hom.app U ((sy.inv.app M).hom.app U x) = x at hv
    exact h.symm.trans (heq_of_eq hv)
  have hri (M : Modules X C) (U : Y.Etaleᵒᵖ)
      (x : (e.toDirectImage.push.obj M).val.obj (op (n, U.unop))) :
      HEq ((r.ordinary.inv.app M).val.app (op (n, U.unop)) x) x := by
    have h := r.sections M n U ((r.ordinary.inv.app M).val.app (op (n, U.unop)) x)
    have he := congrArg (fun f ↦ f.val.app (op (n, U.unop)))
      (r.ordinary.inv_hom_id_app M)
    have hv := ConcreteCategory.congr_hom he x
    change (r.ordinary.hom.app M).val.app (op (n, U.unop))
      ((r.ordinary.inv.app M).val.app (op (n, U.unop)) x) = x at hv
    exact h.symm.trans (heq_of_eq hv)
  intro M
  change (Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
      ((mateEquiv e.adjunction ac
        (TwoSquare.mk _ _ _ _ ec.inverse.hom)).app M) ≫
      (mateEquiv ac ab (TwoSquare.mk _ _ _ _ z.hom)).app _ ≫
      (lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g).map (sx.inv.app M) =
    sy.inv.app (e.toDirectImage.push.obj M) ≫
      (level Y B n).map ((mateEquiv e.adjunction d.adjunction
        (TwoSquare.mk _ _ _ _ r.inverseImage.hom)).app M) ≫
      (mateEquiv d.adjunction ab
        (TwoSquare.mk _ _ _ _ eb.inverse.hom)).app _
  rw [hc, hz, hr, hb]
  ext U x
  change ((sx.inv.app M).hom.app
    ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U))
      (((ec.ordinary.hom.app M).hom.app U) x) =
    ((eb.ordinary.hom.app ((res (ringMap X a)).obj M)).hom.app U)
      (((r.ordinary.inv.app M).val.app (op (n, U.unop)))
        (((sy.inv.app (e.toDirectImage.push.obj M)).hom.app U) x))
  exact eq_of_heq (((hxi M _ _).trans (ec.sections M U x)).trans
    ((eb.sections _ U _).trans ((hri M U _).trans (hyi _ U x))).symm)

attribute [local instance] Image.inverseAdditive Image.inverseLimits
  Image.inverseColimits Image.pushAdditive OpenImage.extensionAdditive
  OpenImage.extensionLimits OpenImage.extensionColimits

private def scalarEvaluationDerived (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {n : ℕ}
    (eb : Evaluation W B n) (ec : Evaluation W C n)
    (s : res (ringMap W a) ⋙ level W B n ≅ level W C n ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (a.app (op n)).hom) :
    restriction W a ⋙ eb.E ≅ ec.E ⋙
      Sheaf.derivedRestrictScalars W.smallEtaleTopology (a.app (op n)).hom :=
  letI := eb.additive
  letI := eb.limits
  letI := eb.colimits
  letI := ec.additive
  letI := ec.limits
  letI := ec.colimits
  Functor.mapDerivedCategorySquareIso s

section
attribute [local irreducible] upperStar

private theorem restriction_exact_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    scalarRestrictionDirectImageMap φ f =
      (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom)
        ) := by
  rw [mapDerivedUpperStarLowerStarAdjunction_eq, mapDerivedUpperStarLowerStarAdjunction_eq]
  ext K
  simp only [scalarRestrictionDirectImageMap, scalarRestrictionPullbackIso,
    mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.id_comp, Functor.comp_map,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id]

end

attribute [local irreducible] eqToHom in
private theorem properCube
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l)
    (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
    (M : Derived c.Z C.rings) :
    (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).proper.R.obj M) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
          ((t.supportEvaluation C n).proper.derived.hom.app M) ≫
        (scalarRestrictionDirectImageMap (a.app (op n)).hom c.g).app
          ((t.evaluationZ C n).E.obj M) =
      (t.evaluationY B n).E.map ((t.restriction a).proper.derived.hom.app M) ≫
        (t.supportEvaluation B n).proper.derived.hom.app ((restriction c.Z a).obj M) ≫
        (lowerStar (ModuleCat.{u + 1} (B.rings.obj (op n)))
          c.g).rightDerivedFunctor.map
          ((scalarEvaluationDerived c.Z (t.evaluationZ B n) (t.evaluationZ C n)
            (ordinaryScalarEvaluation c.Z a n)).hom.app M) := by
  have := (t.evaluationZ B n).additive
  have := (t.evaluationZ B n).limits
  have := (t.evaluationZ B n).colimits
  have := (t.evaluationZ C n).additive
  have := (t.evaluationZ C n).limits
  have := (t.evaluationZ C n).colimits
  have := (t.evaluationY B n).additive
  have := (t.evaluationY B n).limits
  have := (t.evaluationY B n).colimits
  have := (t.evaluationY C n).additive
  have := (t.evaluationY C n).limits
  have := (t.evaluationY C n).colimits
  let r := (t.restriction a).proper
  let eb := (t.supportEvaluation B n).proper
  let ec := (t.supportEvaluation C n).proper
  let sx := ordinaryScalarEvaluation c.Z a n
  let sy := (t.scalarEvaluationY a n).ordinary
  let z := upperStarRestrictScalarsIsoSheaf (a.app (op n)).hom c.g
  have hi := ordinaryInverseCube a (t.support B).proper (t.support C).proper r n
    (t.evaluationZ B n) (t.evaluationZ C n) (t.evaluationY B n) (t.evaluationY C n)
    _ _ _ _ eb ec sx sy (ordinaryScalarEvaluation_sections c.Z a n)
    (t.scalarEvaluationY a n).sections z (underived_mate (a.app (op n)).hom c.g)
  have hl := Functor.mapDerivedCategory_exactCube
    (level Y C.rings n)
    (Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom)
    (upperStar (ModuleCat.{u + 1} (B.rings.obj (op n))) c.g)
    (res (ringMap Y a)) (level Y B.rings n) (t.support B).proper.inverse
    (level c.Z B.rings n) (t.support C).proper.inverse (res (ringMap c.Z a))
    (upperStar (ModuleCat.{u + 1} (C.rings.obj (op n))) c.g)
    (Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom)
    (level c.Z C.rings n) sy.symm eb.inverse r.inverseImage z ec.inverse sx.symm hi
  let sz := scalarEvaluationDerived c.Z (t.evaluationZ B n) (t.evaluationZ C n) sx
  have hc : ∀ N : Derived Y C.rings,
      (upperStar (ModuleCat.{u + 1} (B.rings.obj (op n))) c.g).mapDerivedCategory.map
          ((t.scalarEvaluationY a n).restriction.inv.app N) ≫
        eb.derivedInverse.hom.app ((restriction Y a).obj N) ≫
        (t.evaluationZ B n).E.map (r.derivedInverse.hom.app N) =
      (Functor.mapDerivedCategorySquareIso z).hom.app ((t.evaluationY C n).E.obj N) ≫
        (Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
          (ec.derivedInverse.hom.app N) ≫ sz.inv.app ((t.support C).proper.P.obj N) := by
    intro N
    have h := NatTrans.congr_app hl N
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.square_symm_hom, ← r.derivedInverse_termwise,
      ← eb.derivedInverse_termwise, ← ec.derivedInverse_termwise,
      ← (t.scalarEvaluationY a n).restriction_termwise, scalarEvaluationDerived,
      sz, sx, sy, Category.assoc] using h
  have h := exchangeMate_cube
    (t.support C).proper.derivedAdjunction (t.support B).proper.derivedAdjunction
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (C.rings.obj (op n)))
      c.g).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (B.rings.obj (op n)))
      c.g).mapDerivedCategoryRightDerivedAdjunction
    (t.evaluationY C n).E (t.evaluationZ C n).E
    (t.evaluationY B n).E (t.evaluationZ B n).E
    ec.derivedInverse.symm (t.scalarEvaluationY a n).restriction sz eb.derivedInverse.symm
    r.derivedInverse.hom (Functor.mapDerivedCategorySquareIso z).hom hc M
  rw [restriction_exact_mate]
  simpa only [Iso.symm_inv, ← r.derived_mate, ← eb.derived_mate, ← ec.derived_mate,
    mapDerivedUpperStarLowerStarAdjunction, r, eb, ec, sz, sx, z] using h.symm

attribute [local irreducible] eqToHom in
private theorem openCube
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l)
    (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
    (N : Derived X C.rings) :
    (scalarEvaluationDerived c.Z (t.evaluationZ B n) (t.evaluationZ C n)
      (ordinaryScalarEvaluation c.Z a n)).hom.app ((t.support C).openImage.J.obj N) ≫
        (Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
          ((t.supportEvaluation C n).openImage.derived.hom.app N) ≫
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso
          (a.app (op n)).hom c.i).inv.app ((t.evaluationX C n).E.obj N) =
      (t.evaluationZ B n).E.map ((t.restriction a).openImage.derived.inv.app N) ≫
        (t.supportEvaluation B n).openImage.derived.hom.app ((restriction X a).obj N) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} (B.rings.obj (op n)))
          c.i).mapDerivedCategory.map ((t.scalarEvaluationX a n).restriction.hom.app N) := by
  let := (t.evaluationX B n).additive
  let := (t.evaluationX B n).limits
  let := (t.evaluationX B n).colimits
  let := (t.evaluationX C n).additive
  let := (t.evaluationX C n).limits
  let := (t.evaluationX C n).colimits
  let := (t.evaluationZ B n).additive
  let := (t.evaluationZ B n).limits
  let := (t.evaluationZ B n).colimits
  let := (t.evaluationZ C n).additive
  let := (t.evaluationZ C n).limits
  let := (t.evaluationZ C n).colimits
  let r := (t.restriction a).openImage
  let eb := (t.supportEvaluation B n).openImage
  let ec := (t.supportEvaluation C n).openImage
  let sx := (t.scalarEvaluationX a n).ordinary
  let sy := ordinaryScalarEvaluation c.Z a n
  let z := Iso.refl (Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom ⋙
    openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
  let zb := openImmersionLowerShriekRestrictScalarsIso (a.app (op n)).hom c.i
  have hi := ordinaryInverseCube a (t.support B).openImage.toImage
    (t.support C).openImage.toImage r.image n
    (t.evaluationX B n) (t.evaluationX C n) (t.evaluationZ B n) (t.evaluationZ C n)
    _ _ _ _ eb.image ec.image sx sy (t.scalarEvaluationX a n).sections
    (ordinaryScalarEvaluation_sections c.Z a n) z (openRestrictionMate (a.app (op n)).hom c.i)
  have hc : ∀ M : Modules c.Z C.rings,
      (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
          (ec.image.inverse.inv.app M) ≫
        z.inv.app ((level c.Z C.rings n).obj M) ≫
          (openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
            (sy.inv.app M) =
        sx.inv.app ((t.support C).openImage.inverse.obj M) ≫
          (level X B.rings n).map (r.image.inverseImage.inv.app M) ≫
          eb.image.inverse.inv.app ((res (ringMap c.Z a)).obj M) := by
    intro M
    have hi' :
        (openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
            (sy.inv.app M) ≫ eb.image.inverse.hom.app ((res (ringMap c.Z a)).obj M) ≫
            (level X B.rings n).map (r.image.inverseImage.hom.app M) =
          (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
            (ec.image.inverse.hom.app M) ≫
            sx.inv.app ((t.support C).openImage.inverse.obj M) :=
      (hi M).trans (Category.id_comp _)
    have hh := Functor.square_reverse (level X B.rings n)
      ((Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).mapIso
        (ec.image.inverse.app M))
      (eb.image.inverse.app ((res (ringMap c.Z a)).obj M))
      (r.image.inverseImage.app M)
      ((openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
        (sy.inv.app M))
      (sx.inv.app ((t.support C).openImage.inverse.obj M)) hi'
    calc
      _ = (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
          (ec.image.inverse.inv.app M) ≫
          (openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
            (sy.inv.app M) := by
        exact congrArg
          (fun q ↦ (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
            (ec.image.inverse.inv.app M) ≫ q) (Category.id_comp _)
      _ = _ := by simpa only [Functor.mapIso_inv, Iso.app_inv] using hh
  have ho : ∀ M : Modules X C.rings,
      (openImmersionLowerShriek (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
          (sx.inv.app M) ≫ eb.ordinary.inv.app ((res (ringMap X a)).obj M) ≫
          (level c.Z B.rings n).map (r.ordinary.hom.app M) =
        zb.hom.app ((level X C.rings n).obj M) ≫
          (Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
            (ec.ordinary.inv.app M) ≫ sy.inv.app ((t.support C).openImage.extension.obj M) := by
    apply mateCubeReflects (t.support C).openImage.openAdjunction
      (t.support B).openImage.openAdjunction
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
      (TwoSquare.mk _ _ _ _ r.ordinary.hom) (TwoSquare.mk _ _ _ _ zb.hom)
      (TwoSquare.mk _ _ _ _ ec.ordinary.inv) (TwoSquare.mk _ _ _ _ eb.ordinary.inv)
      sx.symm sy.symm
    have hr : (mateEquiv (t.support C).openImage.openAdjunction
        (t.support B).openImage.openAdjunction
        (TwoSquare.mk _ _ _ _ r.ordinary.hom)) = r.image.inverseImage.inv := by
      rw [r.mate]
      exact (Equiv.apply_symm_apply _ _)
    have hb : (mateEquiv (t.support B).openImage.openAdjunction
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
        (TwoSquare.mk _ _ _ _ eb.ordinary.inv)) = eb.image.inverse.inv := by
      rw [eb.mate]
      exact (Equiv.apply_symm_apply _ _)
    have he : (mateEquiv (t.support C).openImage.openAdjunction
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
        (TwoSquare.mk _ _ _ _ ec.ordinary.inv)) = ec.image.inverse.inv := by
      rw [ec.mate]
      exact (Equiv.apply_symm_apply _ _)
    intro M
    change (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
        ((mateEquiv (t.support C).openImage.openAdjunction
          (openImmersionLowerShriekAdjunction
            (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
          (TwoSquare.mk _ _ _ _ ec.ordinary.inv)).app M) ≫
        (mateEquiv
          (openImmersionLowerShriekAdjunction
            (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
          (openImmersionLowerShriekAdjunction
            (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
          (TwoSquare.mk _ _ _ _ zb.hom)).app
            ((level c.Z C.rings n).obj M) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
          (sy.inv.app M) =
      sx.inv.app ((t.support C).openImage.inverse.obj M) ≫
        (level X B.rings n).map
          ((mateEquiv (t.support C).openImage.openAdjunction
            (t.support B).openImage.openAdjunction
            (TwoSquare.mk _ _ _ _ r.ordinary.hom)).app M) ≫
        (mateEquiv (t.support B).openImage.openAdjunction
          (openImmersionLowerShriekAdjunction
            (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
          (TwoSquare.mk _ _ _ _ eb.ordinary.inv)).app
            ((res (ringMap c.Z a)).obj M)
    rw [he, hr, hb]
    dsimp only [zb]
    rw [openExtensionMate]
    exact hc M
  have hl := Functor.mapDerivedCategory_exactCube
    (level X C.rings n)
    (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom)
    (openImmersionLowerShriek (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
    (res (ringMap X a)) (level X B.rings n) (t.support B).openImage.extension
    (level c.Z B.rings n) (t.support C).openImage.extension (res (ringMap c.Z a))
    (openImmersionLowerShriek (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
    (Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom)
    (level c.Z C.rings n) sx.symm eb.ordinary.symm r.ordinary zb ec.ordinary.symm sy.symm ho
  let sz := scalarEvaluationDerived c.Z (t.evaluationZ B n) (t.evaluationZ C n) sy
  have hd :
      (openImmersionLowerShriek (ModuleCat.{u + 1} (B.rings.obj (op n)))
        c.i).mapDerivedCategory.map ((t.scalarEvaluationX a n).restriction.inv.app N) ≫
        eb.derived.inv.app ((restriction X a).obj N) ≫
        (t.evaluationZ B n).E.map (r.derived.hom.app N) =
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso
        (a.app (op n)).hom c.i).hom.app ((t.evaluationX C n).E.obj N) ≫
        (Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
          (ec.derived.inv.app N) ≫ sz.inv.app ((t.support C).openImage.J.obj N) := by
    have h := NatTrans.congr_app hl N
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.square_symm_hom, ← (t.scalarEvaluationX a n).restriction_termwise,
      OpenEvaluation.derived, RestrictionOpen.derived, scalarEvaluationDerived,
      derivedRestrictScalarsCompOpenImmersionLowerShriekIso, sz, sx, sy, zb,
      Category.assoc] using h
  have he :
      (openImmersionLowerShriek (ModuleCat.{u + 1} (B.rings.obj (op n)))
        c.i).mapDerivedCategory.mapIso ((t.scalarEvaluationX a n).restriction.symm.app N) ≪≫
          eb.derived.symm.app ((restriction X a).obj N) ≪≫
          (t.evaluationZ B n).E.mapIso (r.derived.app N) =
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso
        (a.app (op n)).hom c.i).app ((t.evaluationX C n).E.obj N) ≪≫
          (Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).mapIso
            (ec.derived.symm.app N) ≪≫ sz.symm.app ((t.support C).openImage.J.obj N) :=
    Iso.ext hd
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
    sz, sy, ec, eb, r, Category.assoc] using (congrArg Iso.inv he).symm

-- Pasting unfolds the support functors and normalizes the resulting derived object types.
attribute [local irreducible] eqToHom in
private theorem supportCube
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l)
    (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
    (sz : restriction c.Z a ⋙ (t.evaluationZ B n).E ≅
      (t.evaluationZ C n).E ⋙
        Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom)
    (hp : ∀ M : Derived c.Z C.rings,
      (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).proper.R.obj M) ≫
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
            ((t.supportEvaluation C n).proper.derived.hom.app M) ≫
          (scalarRestrictionDirectImageMap (a.app (op n)).hom c.g).app
            ((t.evaluationZ C n).E.obj M) =
        (t.evaluationY B n).E.map ((t.restriction a).proper.derived.hom.app M) ≫
          (t.supportEvaluation B n).proper.derived.hom.app ((restriction c.Z a).obj M) ≫
          (lowerStar (ModuleCat.{u + 1} (B.rings.obj (op n)))
            c.g).rightDerivedFunctor.map (sz.hom.app M))
    (ho : ∀ N : Derived X C.rings,
      sz.hom.app ((t.support C).openImage.J.obj N) ≫
          (Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
            ((t.supportEvaluation C n).openImage.derived.hom.app N) ≫
          (derivedRestrictScalarsCompOpenImmersionLowerShriekIso
            (a.app (op n)).hom c.i).inv.app ((t.evaluationX C n).E.obj N) =
        (t.evaluationZ B n).E.map ((t.restriction a).openImage.derived.inv.app N) ≫
          (t.supportEvaluation B n).openImage.derived.hom.app
            ((restriction X a).obj N) ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} (B.rings.obj (op n)))
            c.i).mapDerivedCategory.map
              ((t.scalarEvaluationX a n).restriction.hom.app N))
    (N : Derived X C.rings) :
    (t.evaluationY B n).E.map ((t.restriction a).iso.hom.app N) ≫
        (t.supportEvaluation B n).iso.hom.app ((restriction X a).obj N) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (B.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).restriction.hom.app N) =
      (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).F.obj N) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
          ((t.supportEvaluation C n).iso.hom.app N) ≫
        (singleRestriction (a.app (op n)) c).app ((t.evaluationX C n).E.obj N) := by
  have hn := (t.supportEvaluation B n).proper.derived.hom.naturality
    ((t.restriction a).openImage.derived.inv.app N)
  have ht := (scalarRestrictionDirectImageMap (a.app (op n)).hom c.g).naturality
    ((t.supportEvaluation C n).openImage.derived.hom.app N)
  dsimp only [Functor.comp_map] at hn ht
  have ho' := (lowerStar (ModuleCat.{u + 1} (B.rings.obj (op n)))
    c.g).rightDerivedFunctor.congr_map (ho N)
  simp only [Functor.map_comp, Category.assoc] at ho'
  dsimp only [Support.F]
  simp only [SupportEvaluation.iso, RestrictionSupport.iso, singleRestriction,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Functor.map_id, Category.assoc]
  erw [reassoc_of% hn, ← ho',
    ← reassoc_of% (hp ((t.support C).openImage.J.obj N)), reassoc_of% ht]

attribute [local irreducible] eqToHom in
/-- The forward compact-support restriction evaluation cube.

Source: Zheng Construction 4.1 and Lemma 5.16; Stacks Tag 0GL6.
Proof: paste the normalized proper and open restriction comparisons, using
sectionwise identity maps and their inverse-image and right-adjoint mates; exact
localization preserves the resulting square. Naturality of the proper and open
comparisons gives the displayed forward cube. This is the forward form before
cancelling the support evaluation isomorphism and replacing the canonical
single-ring restriction by an arbitrary `d` with `hd`.
(blueprint: lem-pur-etale-system-restriction-evaluation-forward)
-/
theorem etaleSystemRestriction_evaluation_forward
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l)
    (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
    (d : rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (C.rings.obj (op n))) c ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology (a.app (op n)).hom ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (B.rings.obj (op n))) c)
    (hd : d.hom = singleRestriction (a.app (op n)) c)
    (N : Derived X C.rings) :
    ((t.supportEvaluation B n).iso.inv.app ((restriction X a).obj N) ≫
        (t.evaluationY B n).E.map ((t.restriction a).iso.inv.app N) ≫
        (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).F.obj N)) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
        ((t.supportEvaluation C n).iso.hom.app N) =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (B.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).restriction.hom.app N) ≫
        d.inv.app ((t.evaluationX C n).E.obj N) := by
  let sz := scalarEvaluationDerived c.Z (t.evaluationZ B n) (t.evaluationZ C n)
    (ordinaryScalarEvaluation c.Z a n)
  have hc := supportCube c l t B C a n sz
    (properCube c l t B C a n) (openCube c l t B C a n) N
  let e := (t.evaluationY B n).E.mapIso ((t.restriction a).iso.app N) ≪≫
    (t.supportEvaluation B n).iso.app ((restriction X a).obj N)
  let g := (t.scalarEvaluationY a n).restriction.hom.app ((t.support C).F.obj N) ≫
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology (a.app (op n)).hom).map
      ((t.supportEvaluation C n).iso.hom.app N)
  have hd' := NatTrans.congr_app hd ((t.evaluationX C n).E.obj N)
  have hh : e.hom ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (B.rings.obj (op n))) c).map
          ((t.scalarEvaluationX a n).restriction.hom.app N) =
        g ≫ (d.app ((t.evaluationX C n).E.obj N)).hom := by
    simpa only [e, g, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc, hd'] using hc
  have h' := ((d.app ((t.evaluationX C n).E.obj N)).comp_inv_eq).2 hh
  have h'' := e.inv_comp_eq.mpr
    (by simpa only [Category.assoc] using h'.symm)
  simpa only [e, g, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Category.assoc] using h''

end AlgebraicGeometry.Etale.SystemProjection
