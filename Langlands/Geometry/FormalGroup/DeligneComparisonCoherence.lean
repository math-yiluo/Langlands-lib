import Langlands.Geometry.FormalGroup.DeligneInverseImageCoherence

/-! # Identity and composition of the ordinary-to-structural comparison -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.TwoSquare

variable {O : Type u} [CommRing O] {S S' S'' : Scheme.{u}}

/-- The canonical comparison as a square between the actual scalar-forgetting
functors and the two pullbacks. Its mates express the coherence proofs. -/
def structuralPullbackSquare (f : S' ⟶ S) (φ : O →+* Γ(S, ⊤)) :
    TwoSquare (structuralOSheafFunctor S φ) (Scheme.Modules.pullback f)
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base)
      (structuralOSheafFunctor S' (pulledGlobalScalar f φ)) :=
  structuralPullbackComparison f φ

/-- The actual ordinary-to-structural comparison is the mate of the actual
pushforward coefficient comparison. -/
theorem structuralPullbackComparison_eq_mate (f : S' ⟶ S) (φ : O →+* Γ(S, ⊤)) :
    structuralPullbackComparison f φ =
      ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base)).symm
        (TwoSquare.mk _ _ _ _ (structuralPushforwardIso f φ).hom)).natTrans := by
  apply NatTrans.ext
  funext M
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O)
    f.base).homEquiv _ _).injective
  dsimp only [structuralPullbackComparison]
  rw [Equiv.apply_symm_apply]
  exact (unit_mateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base)
    (TwoSquare.mk _ _ _ _ (structuralPushforwardIso f φ).hom) M)

private theorem mateEquiv_identity {A B : Type*} [Category* A] [Category* B]
    (U : A ⥤ B) :
    mateEquiv Adjunction.id Adjunction.id (TwoSquare.vId U) = TwoSquare.vId U := by
  ext M
  simp [mateEquiv, TwoSquare.vId]

/-- The canonical comparison agrees with identity pullback. -/
theorem structuralPullbackComparison_id (φ : O →+* Γ(S, ⊤)) :
    structuralPullbackComparison (𝟙 S) φ ≫
        Functor.whiskerRight (Scheme.Modules.pullbackId S).hom
          (structuralOSheafFunctor S φ) =
      Functor.whiskerLeft (structuralOSheafFunctor S φ)
        (inverseImageIdIso O (S : TopCat)).hom := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (𝟙 (S : TopCat))
  let U := structuralOSheafFunctor S φ
  let q : TwoSquare U (Scheme.Modules.pullback (𝟙 S))
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) (𝟙 (S : TopCat))) U :=
    structuralPullbackComparison (𝟙 S) φ
  have hq : mateEquiv a b q = (structuralPushforwardIso (𝟙 S) φ).hom := by
    rw [show q = ((mateEquiv a b).symm
      (structuralPushforwardIso (𝟙 S) φ).hom) from
        structuralPullbackComparison_eq_mate (𝟙 S) φ]
    exact (mateEquiv a b).apply_symm_apply _
  change (q.whiskerLeft (Scheme.Modules.pullbackId S).hom).natTrans =
    ((TwoSquare.vId U).whiskerRight (inverseImageIdIso O (S : TopCat)).hom).natTrans
  apply (mateEquiv Adjunction.id b).injective
  rw [conjugateEquiv_mateEquiv_vcomp Adjunction.id a b,
    mateEquiv_conjugateEquiv_vcomp Adjunction.id Adjunction.id b,
    hq, Scheme.Modules.conjugateEquiv_pullbackId_hom]
  have hb : conjugateEquiv Adjunction.id b (inverseImageIdIso O (S : TopCat)).hom =
      𝟙 _ := by
    exact (conjugateEquiv Adjunction.id b).apply_symm_apply (𝟙 _)
  rw [hb, mateEquiv_identity]
  ext M
  apply Sheaf.hom_ext
  ext V x
  rfl

/-- The canonical comparison agrees with composition of pullbacks. -/
theorem structuralPullbackComparison_comp (f : S' ⟶ S) (g : S'' ⟶ S')
    (φ : O →+* Γ(S, ⊤)) :
    Functor.whiskerLeft (structuralOSheafFunctor S φ)
        (inverseImageCompIso O f.base g.base).hom ≫
        structuralPullbackComparison (g ≫ f) φ =
      Functor.whiskerRight (structuralPullbackComparison f φ)
          (TopCat.Sheaf.pullback (ModuleCat.{u} O) g.base) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback f)
          (structuralPullbackComparison g (pulledGlobalScalar f φ)) ≫
        Functor.whiskerRight (Scheme.Modules.pullbackComp g f).hom
          (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)) := by
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let ag := Scheme.Modules.pullbackPushforwardAdjunction g
  let ac := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  let bf := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base
  let bg := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) g.base
  let bc := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) (g ≫ f).base
  let qf : TwoSquare (structuralOSheafFunctor S φ) (Scheme.Modules.pullback f)
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base)
      (structuralOSheafFunctor S' (pulledGlobalScalar f φ)) :=
    structuralPullbackComparison f φ
  let qg : TwoSquare (structuralOSheafFunctor S' (pulledGlobalScalar f φ))
      (Scheme.Modules.pullback g) (TopCat.Sheaf.pullback (ModuleCat.{u} O) g.base)
      (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)) :=
    structuralPullbackComparison g (pulledGlobalScalar f φ)
  let qc : TwoSquare (structuralOSheafFunctor S φ) (Scheme.Modules.pullback (g ≫ f))
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) (g ≫ f).base)
      (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)) :=
    structuralPullbackComparison (g ≫ f) φ
  have hf : mateEquiv af bf qf = (structuralPushforwardIso f φ).hom := by
    rw [show qf = ((mateEquiv af bf).symm (structuralPushforwardIso f φ).hom) from
      structuralPullbackComparison_eq_mate f φ]
    exact (mateEquiv af bf).apply_symm_apply _
  have hg : mateEquiv ag bg qg =
      (structuralPushforwardIso g (pulledGlobalScalar f φ)).hom := by
    rw [show qg = ((mateEquiv ag bg).symm
      (structuralPushforwardIso g (pulledGlobalScalar f φ)).hom) from
        structuralPullbackComparison_eq_mate g (pulledGlobalScalar f φ)]
    exact (mateEquiv ag bg).apply_symm_apply _
  have hc : mateEquiv ac bc qc = (structuralPushforwardIso (g ≫ f) φ).hom := by
    rw [show qc = ((mateEquiv ac bc).symm (structuralPushforwardIso (g ≫ f) φ).hom) from
      structuralPullbackComparison_eq_mate (g ≫ f) φ]
    exact (mateEquiv ac bc).apply_symm_apply _
  have h : qc.whiskerLeft (Scheme.Modules.pullbackComp g f).inv =
      (qf ≫ᵥ qg).whiskerRight (inverseImageCompIso O f.base g.base).inv := by
    apply (mateEquiv (af.comp ag) bc).injective
    rw [conjugateEquiv_mateEquiv_vcomp (af.comp ag) ac bc,
      mateEquiv_conjugateEquiv_vcomp (af.comp ag) (bf.comp bg) bc,
      mateEquiv_hcomp af bf ag bg, hf, hg, hc]
    have ha : conjugateEquiv (af.comp ag) ac (Scheme.Modules.pullbackComp g f).inv =
        (Scheme.Modules.pushforwardComp g f).hom :=
      SheafOfModules.conjugateEquiv_pullbackComp_inv.{u}
        f.toRingCatSheafHom g.toRingCatSheafHom
    have hb : conjugateEquiv (bf.comp bg) bc
        (inverseImageCompIso O f.base g.base).inv = 𝟙 _ := by
      exact (conjugateEquiv (bf.comp bg) bc).apply_symm_apply (𝟙 _)
    rw [ha, hb]
    ext M
    apply Sheaf.hom_ext
    ext V x
    rfl
  have he := congrArg (fun q => q.natTrans) h
  apply NatTrans.ext
  funext M
  have hx := congrArg (fun k => k.app M) he
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hx
  simp only [Category.id_comp, Category.comp_id] at hx
  apply (cancel_mono ((structuralOSheafFunctor S''
    (pulledGlobalScalar (g ≫ f) φ)).map
      ((Scheme.Modules.pullbackComp g f).inv.app M))).mp
  change
    ((inverseImageCompIso O f.base g.base).hom.app
        ((structuralOSheafFunctor S φ).obj M) ≫ qc.natTrans.app M) ≫
      (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)).map
        ((Scheme.Modules.pullbackComp g f).inv.app M) =
    ((TopCat.Sheaf.pullback (ModuleCat.{u} O) g.base).map (qf.natTrans.app M) ≫
      qg.natTrans.app ((Scheme.Modules.pullback f).obj M) ≫
      (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)).map
        ((Scheme.Modules.pullbackComp g f).hom.app M)) ≫
      (structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)).map
        ((Scheme.Modules.pullbackComp g f).inv.app M)
  rw [Category.assoc, hx]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  exact (Category.comp_id _).symm.trans
    (congrArg (fun k =>
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) g.base).map (qf.natTrans.app M) ≫
        qg.natTrans.app ((Scheme.Modules.pullback f).obj M) ≫ k)
      ((structuralOSheafFunctor S'' (pulledGlobalScalar (g ≫ f) φ)).map_id
        ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g).obj M)).symm)

end Langlands.DeligneFormalSpace
