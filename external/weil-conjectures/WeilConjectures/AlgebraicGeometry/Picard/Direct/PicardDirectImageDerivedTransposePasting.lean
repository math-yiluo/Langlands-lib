/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageDerivedTranspose
import WeilConjectures.AlgebraicGeometry.Picard.PicardCoefficientTransposePasting
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedUnitNormalizationComposition
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageDerivedTransposeFactorization

/-! # Successive base change before fibre-unit normalization

## References

* Stacks Project, Tags 08HY and 0D5S
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private theorem pasteWithSection
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (Li : C₁ ⥤ C₂) (Lt : C₀ ⥤ C₁) (Lt' : C₀ ⥤ C₂)
    (Lp : C₁ ⥤ C₃) (Lp' : C₂ ⥤ C₄) (Lj : C₃ ⥤ C₄)
    (C : Lt ⋙ Li ≅ Lt') (D : Li ⋙ Lp' ⟶ Lp ⋙ Lj)
    {O E : C₀} {U : C₁} {U' : C₂} {N : C₃} {N' : C₄}
    (e : Lt.obj O ≅ U) (e' : Lt'.obj O ≅ U')
    (ξ : Lt.obj O ⟶ Lt.obj E) (s : Li.obj U ⟶ U')
    (τ : Lp.obj (Lt.obj E) ⟶ N) (τ' : Lp'.obj (Lt'.obj E) ⟶ N')
    (b : Lj.obj N ⟶ N')
    (hc : D.app (Lt.obj E) ≫ Lj.map τ ≫ b = Lp'.map (C.hom.app E) ≫ τ')
    (hu : Li.map e.inv ≫ C.hom.app O = s ≫ e'.inv) :
    D.app U ≫ Lj.map (Lp.map (e.inv ≫ ξ) ≫ τ) ≫ b =
      Lp'.map s ≫
        (Lp'.map (e'.inv ≫ (C.inv.app O ≫ Li.map ξ ≫ C.hom.app E)) ≫ τ') := by
  have hr : Li.map (e.inv ≫ ξ) ≫ C.hom.app E =
      s ≫ e'.inv ≫ (C.inv.app O ≫ Li.map ξ ≫ C.hom.app E) := by
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp] using
      congrArg (fun q ↦ q ≫ C.inv.app O ≫ Li.map ξ ≫ C.hom.app E) hu
  have hn := D.naturality (e.inv ≫ ξ)
  change Lp'.map (Li.map (e.inv ≫ ξ)) ≫ D.app (Lt.obj E) =
    D.app U ≫ Lj.map (Lp.map (e.inv ≫ ξ)) at hn
  calc
    _ = Lp'.map (Li.map (e.inv ≫ ξ)) ≫
        (D.app (Lt.obj E) ≫ Lj.map τ ≫ b) := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ q ≫ Lj.map τ ≫ b) hn.symm
    _ = Lp'.map (Li.map (e.inv ≫ ξ) ≫ C.hom.app E) ≫ τ' := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ Lp'.map (Li.map (e.inv ≫ ξ)) ≫ q) hc
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ Lp'.map q ≫ τ') hr

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

-- Keep categorical comparison choices folded during naturality rewriting.
/-- The derived adjoint of a test morphism respects successive base change.
The source is a twice-derived pullback of O_T[0], not a module on the fibre. -/
theorem picardDirectImageDerivedTranspose_pasting
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (h : i ≫ t = t')
    (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k))
    (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k))
    (hj₂ : j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
    let U := SheafOfModules.unit (moduleRings T.toRingedSpace)
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj U
    let p := pullback.snd f (t ≫ k)
    let p' := pullback.snd f (t' ≫ k)
    let D := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) p' i).hom.app A ≫
      eqToHom (congrArg (fun q ↦ (derivedPullback q).obj A) hj₂.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) j p).inv.app A
    let c := (conjugateIsoEquiv
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (t ≫ k)))).comp
          (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
      (Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (t' ≫ k))))).symm
      (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
        Modules.pushforwardCongr hj₁)
    let d := ((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction j)).symm.app N ≪≫ (c.app L).symm
    D ≫ (derivedPullback j).map (picardDirectImageDerivedTranspose f L W k t ξ) ≫
        Modules.canonicalSinglePullbackMap j N ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f (t' ≫ k)).toRingedSpace)) 0).map
            d.hom =
      (derivedPullback p').map
        (Modules.canonicalSinglePullbackMap i U ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).map
              (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)) ≫
        picardDirectImageDerivedTranspose f L W k t'
          (picardDerivedModelRestriction _ i t t' h ξ) := by
  classical
  intro N U A p p' D0 c d
  let τ : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
    picardCoefficientTranspose f L W k
  let e : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback r).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings V.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings V.toRingedSpace)) :=
    picardDerivedUnitNormalization W
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  let O := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings W.toRingedSpace))
  let C := canonicalDerivedPullbackComposition i t ≪≫
    eqToIso (congrArg (fun q : T' ⟶ W ↦ derivedPullback q) h)
  let D : derivedPullback i ⋙ derivedPullback p' ⟶
      derivedPullback p ⋙ derivedPullback j :=
    (canonicalDerivedPullbackComposition p' i).hom ≫
      eqToHom (congrArg (fun q ↦ derivedPullback q) hj₂.symm) ≫
        (canonicalDerivedPullbackComposition j p).inv
  let b := Modules.canonicalSinglePullbackMap j N ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f (t' ≫ k)).toRingedSpace)) 0).map d.hom
  let s := Modules.canonicalSinglePullbackMap i U ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).map
        (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)
  have hf : ∀ {V : Scheme.{v}} (r : V ⟶ W) (ζ : picardDerivedModelSections E r),
      picardDirectImageDerivedTranspose f L W k r ζ =
        (derivedPullback (pullback.snd f (r ≫ k))).map ((e r).inv ≫ ζ) ≫ τ r := by
    intro V r ζ
    exact picardDirectImageDerivedTranspose_factorization f L W k r ζ
  have hc := picardCoefficientTranspose_pasting f L W k i t t' h j hj₁ hj₂
  have hc' : D.app ((derivedPullback t).obj E) ≫ (derivedPullback j).map (τ t) ≫ b =
      (derivedPullback p').map (C.hom.app E) ≫ τ t' := by
    simpa (config := { zetaDelta := false }) only
      [D, NatTrans.comp_app, eqToHom_app, canonicalDerivedSquareComparison,
      Category.assoc] using hc
  have hu : (derivedPullback i).map (e t).inv ≫ C.hom.app O = s ≫ (e t').inv := by
    simpa (config := { zetaDelta := false }) only [e, C, O, U, s, Category.assoc] using
      picardDerivedUnitNormalization_comp i t t' h
  let ξ' := picardDerivedModelRestriction E i t t' h ξ
  change D0 ≫ (derivedPullback j).map
      (picardDirectImageDerivedTranspose f L W k t ξ) ≫ b =
    (derivedPullback p').map s ≫
      picardDirectImageDerivedTranspose f L W k t' ξ'
  have hD : D.app A = D0 := by
    simp only [D, D0, canonicalDerivedPullbackComposition, NatTrans.comp_app, eqToHom_app]
  rw [← hD, hf, hf]
  exact pasteWithSection (derivedPullback i) (derivedPullback t) (derivedPullback t')
    (derivedPullback p) (derivedPullback p') (derivedPullback j) C D
    (e t) (e t') ξ s (τ t) (τ t') b hc' hu

end
end AlgebraicGeometry.Scheme
