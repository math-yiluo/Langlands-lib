/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageDerivedTranspose
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSingleAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit

/-! # The single-module description of the derived transpose

## References

* Stacks Project, Tags 08HY, 079W and 0D5S
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

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

private theorem transposeFromHomology
    {Z T : Scheme.{v}} (p : Z ⟶ T) [HasInjectiveResolutions Z.Modules]
    (V : T.Modules) [SheafOfModules.IsInvertible.{v, v, v} V] (N : Z.Modules)
    (adj : derivedPullback p ⊣ schemeDerivedDirectImage p)
    (compat : ∀ a : (Modules.pullback p).obj V ⟶ N,
      adj.homEquiv _ _ (Modules.canonicalSinglePullbackMap p V ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings Z.toRingedSpace)) 0).map a) =
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).map
            ((Modules.pullbackPushforwardAdjunction p).homEquiv _ _ a) ≫
              Modules.canonicalSingleDirectImageMap p N)
    (q : (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj V ⟶
      (schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings Z.toRingedSpace)) 0).obj N)) :
    (adj.homEquiv _ _).symm q =
      Modules.canonicalSinglePullbackMap p V ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings Z.toRingedSpace)) 0).map
            (((Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm
              ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                  (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).inv.app V ≫
                (DerivedCategory.homologyFunctor
                  (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).map q ≫
                (Modules.canonicalDirectImageH0Iso p N).hom)) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let F := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings Z.toRingedSpace)) 0
  let G := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0
  let z := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0
  let s := Modules.canonicalSinglePullbackMap p V
  have := Modules.isIso_canonicalSinglePullbackMap p V
  let b := F.preimage (inv s ≫ (adj.homEquiv _ _).symm q)
  have hb : s ≫ F.map b = (adj.homEquiv _ _).symm q := by
    simp only [b, Functor.map_preimage, IsIso.hom_inv_id_assoc]
    rfl
  let m := (Modules.pullbackPushforwardAdjunction p).homEquiv _ _ b
  have ht : G.map m ≫ Modules.canonicalSingleDirectImageMap p N = q := by
    rw [← compat b, hb, Equiv.apply_symm_apply]
  have hu := Modules.canonicalDirectImageH0Unit p N
  change H.map (Modules.canonicalSingleDirectImageMap p N) ≫
    (Modules.canonicalDirectImageH0Iso p N).hom = z.hom.app ((Modules.pushforward p).obj N)
      at hu
  have hn := z.hom.naturality m
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hm : m = z.inv.app V ≫ H.map q ≫ (Modules.canonicalDirectImageH0Iso p N).hom := by
    calc
      _ = z.inv.app V ≫ H.map (G.map m) ≫ z.hom.app ((Modules.pushforward p).obj N) := by
        rw [hn]
        simp only [Iso.inv_hom_id_app_assoc]
      _ = _ := by
        rw [← hu]
        simp only [← Functor.map_comp_assoc, ht]
  have hbm : b = ((Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm
      (z.inv.app V ≫ H.map q ≫ (Modules.canonicalDirectImageH0Iso p N).hom) := by
    exact (Equiv.eq_symm_apply _).mpr hm
  rw [hbm] at hb
  exact hb.symm

/-- Taking degree zero and transposing ordinarily recovers the same morphism
as derived transposition, after the canonical single-pullback comparison.
This is a comparison at one test scheme, with no restriction morphism. -/
theorem picardDirectImageDerivedTranspose_single
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T : Scheme.{v}} (t : T ⟶ W)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    picardDirectImageDerivedTranspose f L W k t ξ =
      Modules.canonicalSinglePullbackMap (pullback.snd f (t ≫ k))
        (SheafOfModules.unit (moduleRings T.toRingedSpace)) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) 0).map
          (SheafOfModules.pullbackObjUnitToUnit
            (pullback.snd f (t ≫ k)).toRingCatSheafHom ≫
              picardDirectImageUnitMorphism f L W k t ξ) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let a : pullback f (t ≫ k) ⟶ pullback f k :=
    pullback.lift (pullback.fst f (t ≫ k)) (pullback.snd f (t ≫ k) ≫ t)
      (by rw [Category.assoc]; exact pullback.condition)
  have ha : a ≫ pullback.fst f k = pullback.fst f (t ≫ k) := pullback.lift_fst ..
  have hb : a ≫ pullback.snd f k = pullback.snd f (t ≫ k) ≫ t := pullback.lift_snd ..
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t ≫ k))))).symm
    (Modules.pushforwardComp a (pullback.fst f k) ≪≫ Modules.pushforwardCongr ha)
  let d : (Modules.pullback a).obj M ≅ N :=
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
  let B := schemeDerivedBaseChangeMap (pullback.snd f k) (pullback.snd f (t ≫ k))
    t a hb ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (schemeDerivedDirectImage (pullback.snd f (t ≫ k))).map
        (Modules.canonicalSinglePullbackMap a M ≫
          (DerivedCategory.singleFunctor _ 0).map d.hom)
  let U := SheafOfModules.unit (moduleRings W.toRingedSpace)
  have hU : SheafOfModules.IsInvertible.{v, v, v} U := by
    dsimp [U]
    exact SheafOfModules.instIsInvertibleUnit.{v, v, v}
  let := hU
  have : IsIso (Modules.canonicalSinglePullbackMap t U) :=
    Modules.isIso_canonicalSinglePullbackMap t U
  let e := asIso (Modules.canonicalSinglePullbackMap t U) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit t.toRingCatSheafHom))
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0
  let z := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).app
      (SheafOfModules.unit (moduleRings T.toRingedSpace))
  let : IsGrothendieckAbelian.{v}
      (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  let : EnoughInjectives (pullback f (t ≫ k)).Modules :=
    by
      change EnoughInjectives
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace))
      exact IsGrothendieckAbelian.enoughInjectives.{v, v, v + 1}
  let : HasInjectiveResolutions (pullback f (t ≫ k)).Modules := inferInstance
  let r := Modules.canonicalDirectImageH0Iso (pullback.snd f (t ≫ k)) N
  let m := fun ξ ↦ z.inv ≫ H.map e.inv ≫ H.map ξ ≫ H.map B ≫ r.hom
  let p := pullback.snd f (t ≫ k)
  let adj := Classical.choose (exists_schemeDerivedAdjunction p
    (hAdd := (Classical.choose exists_derivedPullbackComposition) p)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) p)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) p))
  let V := SheafOfModules.unit (moduleRings T.toRingedSpace)
  let : SheafOfModules.IsInvertible.{v, v, v} V := SheafOfModules.instIsInvertibleUnit.{v, v, v}
  have ht := transposeFromHomology p V N adj
    (Modules.canonicalSingleAdjunctionTranspose p V N) (e.inv ≫ ξ ≫ B)
  unfold picardDirectImageDerivedTranspose
  change (adj.homEquiv _ _).symm (e.inv ≫ ξ ≫ B) =
    Modules.canonicalSinglePullbackMap p V ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t ≫ k)).toRingedSpace)) 0).map
        (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom ≫
          (inv (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom) ≫
            ((Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm (m ξ)))
  simp only [IsIso.hom_inv_id_assoc]
  simpa only [m, H, z, r, p, V, Iso.app_inv, Functor.map_comp, Category.assoc] using ht

end
end AlgebraicGeometry.Scheme
