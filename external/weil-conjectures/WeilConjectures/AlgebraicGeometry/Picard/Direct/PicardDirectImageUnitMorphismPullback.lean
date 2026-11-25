/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageUnitMorphism
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSinglePullbackSquare
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSingleAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageDerivedTransposeSingle
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageDerivedTransposePasting
import WeilConjectures.AlgebraicGeometry.PullbackStructureUnitSquare

/-! # Pullback compatibility before evaluation of the canonical unit morphism

## References

* Stacks Project, Tags 08HY and 0D5S
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

section
namespace Modules

set_option maxRecDepth 2048 in
private theorem singlePullback_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    let adj := Classical.choose (exists_schemeDerivedAdjunction f
      (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f))
    let G := DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0
    let b := (pullback f).map a
    let ord := pullbackPushforwardAdjunction f
    have hn := canonicalSingleAdjunctionTranspose f N ((pullback f).obj N) (𝟙 _)
    have hm := canonicalSingleAdjunctionTranspose f M ((pullback f).obj N) b
    have hn' : adj.homEquiv _ _ (canonicalSinglePullbackMap f N) =
        G.map (ord.homEquiv _ _ (𝟙 _)) ≫
          canonicalSingleDirectImageMap f ((pullback f).obj N) := by
      change adj.homEquiv _ _ (canonicalSinglePullbackMap f N ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) 0).map (𝟙 _)) = _ at hn
      erw [CategoryTheory.Functor.map_id, Category.comp_id] at hn
      exact hn
    have ha : a ≫ ord.homEquiv _ _ (𝟙 _) = ord.homEquiv _ _ b := by
      simpa only [b, Category.comp_id] using
        (ord.homEquiv_naturality_left a (𝟙 _)).symm
    apply (adj.homEquiv _ _).injective
    calc
      _ = G.map a ≫ adj.homEquiv _ _ (canonicalSinglePullbackMap f N) :=
        adj.homEquiv_naturality_left _ _
      _ = G.map a ≫ G.map (ord.homEquiv _ _ (𝟙 _)) ≫
          canonicalSingleDirectImageMap f ((pullback f).obj N) := by rw [hn']
      _ = G.map (ord.homEquiv _ _ b) ≫
          canonicalSingleDirectImageMap f ((pullback f).obj N) := by
        rw [← Category.assoc, ← G.map_comp, ha]
      _ = _ := hm.symm

end Modules
end

/-- Compare two factorizations through an epimorphism using a faithful functor. -/
private theorem cancel_single_comparison
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) [H.Faithful]
    {A B B' N : C} {Z : D} (P : Z ⟶ H.obj A) [Epi P]
    (r : Z ⟶ H.obj B) (s : Z ⟶ H.obj B')
    (a : A ⟶ B) (b : B ⟶ N) (c : A ⟶ B') (d : B' ⟶ N)
    (hr : r = P ≫ H.map a) (hs : s = P ≫ H.map c)
    (h : r ≫ H.map b = s ≫ H.map d) : a ≫ b = c ≫ d := by
  apply H.map_injective
  apply (cancel_epi P).mp
  simpa only [Functor.map_comp, Category.assoc, hr, hs] using h

set_option maxRecDepth 2048 in
attribute [local irreducible] Modules.tensorPullback picardDirectImageUnitMorphism in
set_option cleanup.letToHave false in
-- Preserve the explicit signature lets; cleanup expands the large tensor-adjunction choices.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback compatibility of the underlying module morphisms, before evaluating
on sections. No evaluation at 1 or restriction of sections is asserted here. -/
theorem picardDirectImageUnitMorphism_pullback
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
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
            let U := SheafOfModules.unit
              (moduleRings (pullback f (t ≫ k)).toRingedSpace)
            let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
            (adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)).hom.app U ≫
                SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom ≫
                picardDirectImageUnitMorphism f L W k t'
                  (picardDerivedModelRestriction E i t t' h ξ) =
              (Modules.tensorPullback j).map
                (picardDirectImageUnitMorphism f L W k t ξ) ≫ (c.app L).inv := by
  classical
  intro E T T' i t t' h j hj₁ hj₂ c ξ U adj
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let p := pullback.snd f (t ≫ k)
  let p' := pullback.snd f (t' ≫ k)
  let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let V := SheafOfModules.unit (moduleRings T.toRingedSpace)
  let V' := SheafOfModules.unit (moduleRings T'.toRingedSpace)
  let u := SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom
  let u' := SheafOfModules.pullbackObjUnitToUnit p'.toRingCatSheafHom
  let ui := SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom
  let uj := SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom
  let n := picardDirectImageUnitMorphism f L W k t ξ
  let n' := picardDirectImageUnitMorphism f L W k t'
    (picardDerivedModelRestriction E i t t' h ξ)
  let H := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback f (t' ≫ k)).toRingedSpace)) 0
  let A := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj V
  let D := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) p' i).hom.app A ≫
      eqToHom (congrArg (fun q ↦ (derivedPullback q).obj A) hj₂.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) j p).inv.app A
  let b := (Modules.pullbackComp j p).app V ≪≫ (Modules.pullbackCongr hj₂).app V ≪≫
    ((Modules.pullbackComp p' i).app V).symm
  let d := (adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)).symm.app N ≪≫
    (c.app L).symm
  let P := (derivedPullback p').map (Modules.canonicalSinglePullbackMap i V) ≫
    Modules.canonicalSinglePullbackMap p' ((Modules.pullback i).obj V)
  have hsingle := Modules.singlePullback_naturality p' ui
  have hsquare := Modules.canonicalSinglePullbackSquare p i j p' hj₂ V N (u ≫ n)
  have hpaste := picardDirectImageDerivedTranspose_pasting f L W k i t t' h j hj₁ hj₂ ξ
  have ht := picardDirectImageDerivedTranspose_single f L W k t ξ
  have ht' := picardDirectImageDerivedTranspose_single f L W k t'
    (picardDerivedModelRestriction E i t t' h ξ)
  have hleft := congrArg (fun q ↦ D ≫ (derivedPullback j).map q ≫
    Modules.canonicalSinglePullbackMap j N ≫ H.map d.hom) ht
  have hright := congrArg (fun q ↦ (derivedPullback p').map
    (Modules.canonicalSinglePullbackMap i V ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).map ui) ≫ q) ht'
  have hpaste' := hleft.symm.trans (hpaste.trans hright)
  change D ≫ (derivedPullback j).map
      (Modules.canonicalSinglePullbackMap p V ≫
        (DerivedCategory.singleFunctor _ 0).map (u ≫ n)) ≫
      Modules.canonicalSinglePullbackMap j N ≫ H.map d.hom =
    (derivedPullback p').map
      (Modules.canonicalSinglePullbackMap i V ≫
        (DerivedCategory.singleFunctor _ 0).map ui) ≫
      Modules.canonicalSinglePullbackMap p' V' ≫ H.map (u' ≫ n') at hpaste'
  have hsquare' : D ≫ (derivedPullback j).map
      (Modules.canonicalSinglePullbackMap p V ≫
        (DerivedCategory.singleFunctor _ 0).map (u ≫ n)) ≫
      Modules.canonicalSinglePullbackMap j N =
    P ≫ H.map (b.inv ≫ (Modules.pullback j).map (u ≫ n)) := by
      with_reducible
        simpa only [P, D, A, b, H, Category.assoc] using hsquare
  have hsingle' : (derivedPullback p').map
      (Modules.canonicalSinglePullbackMap i V ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).map ui) ≫
      Modules.canonicalSinglePullbackMap p' V' =
    P ≫ H.map ((Modules.pullback p').map ui) := by
    have hn := congrArg (fun q ↦
      (derivedPullback p').map (Modules.canonicalSinglePullbackMap i V) ≫ q) hsingle
    with_reducible
      simpa only [H, P, V, V', Scheme.ringCatSheaf, Modules.pullback,
        Functor.map_comp, Category.assoc] using hn
  let : SheafOfModules.IsInvertible.{v, v, v} V := SheafOfModules.instIsInvertibleUnit.{v, v, v}
  let : SheafOfModules.IsInvertible.{v, v, v} V' := SheafOfModules.instIsInvertibleUnit.{v, v, v}
  let : SheafOfModules.IsInvertible.{v, v, v} ((Modules.pullback i).obj V) :=
    SheafOfModules.IsInvertible.of_iso.{v, v, v} (asIso ui).symm
  let := Modules.isIso_canonicalSinglePullbackMap i V
  let := Modules.isIso_canonicalSinglePullbackMap p' ((Modules.pullback i).obj V)
  have : IsIso P := by dsimp only [P]; infer_instance
  have hm := cancel_single_comparison H P _ _ _ d.hom _ (u' ≫ n') hsquare' hsingle'
    (by simpa only [Category.assoc] using hpaste')
  have hunit := Modules.pullbackStructureUnitSquare p i j p' hj₂
  change b.inv ≫ (Modules.pullback j).map u ≫ uj =
    (Modules.pullback p').map ui ≫ u' at hunit
  have : IsIso u := by dsimp only [u]; infer_instance
  have : IsIso ((Modules.pullback j).map u) := by
    change IsIso ((SheafOfModules.pullback j.toRingCatSheafHom).map u)
    infer_instance
  have : IsIso (b.inv ≫ (Modules.pullback j).map u) := inferInstance
  have hordinary : uj ≫ n' = (Modules.pullback j).map n ≫ d.hom := by
    apply (cancel_epi (b.inv ≫ (Modules.pullback j).map u)).mp
    calc
      _ = ((Modules.pullback p').map ui ≫ u') ≫ n' := by
        simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ n') hunit
      _ = _ := by
        simpa only [Functor.map_comp, Category.assoc] using hm.symm
  let τ := adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)
  have hn := τ.hom.naturality n
  change τ.hom.app U ≫ uj ≫ n' = (Modules.tensorPullback j).map n ≫ (c.app L).inv
  calc
    _ = τ.hom.app U ≫ (Modules.pullback j).map n ≫ d.hom := by
      simpa only [Category.assoc] using
        congrArg (fun q ↦ τ.hom.app U ≫ q) hordinary
    _ = (Modules.tensorPullback j).map n ≫ τ.hom.app N ≫ d.hom := by
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ d.hom) hn.symm
    _ = _ := by
      change (Modules.tensorPullback j).map n ≫ τ.hom.app N ≫ τ.inv.app N ≫
        (c.app L).inv = _
      simp only [Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Scheme
