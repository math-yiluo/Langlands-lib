/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueNormalizationMap
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSinglePullbackSquare
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorSinglePullbackComposition
import WeilConjectures.AlgebraicGeometry.Picard.PicardTensorOrdinaryCoefficientTriangle
import WeilConjectures.AlgebraicGeometry.Picard.PicardOrdinaryResidueCoefficientSquare

/-! # PicardResidueCoefficientSquare

## References

* Stacks Project, Tags 0096, 06YJ, 0A1D, 08HY, 0D5S and 01F7
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace Modules

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

private theorem residue_singlePullback_naturality
    {X Y : Scheme.{v}} (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.derivedPullback f).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
      canonicalSinglePullbackMap f N =
    canonicalSinglePullbackMap f M ≫
      (DerivedCategory.singleFunctor _ 0).map ((pullback f).map a) := by
  exact AlgebraicGeometry.single_naturality f a

end Modules

-- Normalizing the fixed derived single-functor comparisons expands the fibre objects.
set_option maxRecDepth 2048 in
/-- The single-module coefficient square before direct image. -/
theorem picardResidueCoefficientSquare
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (g : T ⟶ W) (t : T' ⟶ S) (r : T ≅ T')
    (h : g ≫ k = r.hom ≫ t)
    (e : pullback (pullback.snd f k) g ≅ pullback f t)
    (hefst : e.hom ≫ pullback.fst f t =
      pullback.fst (pullback.snd f k) g ≫ pullback.fst f k)
    (hesnd : e.hom ≫ pullback.snd f t ≫ r.inv = pullback.snd (pullback.snd f k) g)
    (ei : ∀ i, pullback (pullback.snd (fi i) k) g ≅ pullback (fi i) t)
    (heifst : ∀ i, (ei i).hom ≫ pullback.fst (fi i) t =
      pullback.fst (pullback.snd (fi i) k) g ≫ pullback.fst (fi i) k)
    (heisnd : ∀ i, (ei i).hom ≫ pullback.snd (fi i) t ≫ r.inv =
      pullback.snd (pullback.snd (fi i) k) g)
    (τ : (Modules.tensorPullback (pullback.fst f t)).obj L ≅
      SheafOfModules.unit (pullback f t).ringCatSheaf) :
    let _E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    let _Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))
    let Xs := pullback f t
    let Xis := fun i ↦ pullback (fi i) t
    let _A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings Xs.toRingedSpace)) 0).obj
        (SheafOfModules.unit Xs.ringCatSheaf)
    let _Ai := fun i ↦ (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (Xis i).toRingedSpace)) 0).obj
        (SheafOfModules.unit (Xis i).ringCatSheaf)
    let j := fun i ↦ ((Over.pullback t).map
      (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left
    let τi := fun i ↦
      (picardResidueCoefficientIso f (fi i) (ui i) (hui i) L T' t).symm ≪≫
        (Modules.pullback (j i)).mapIso τ ≪≫ Modules.pullbackObjUnitIso (j i)
    let jW := fun i ↦ ((Over.pullback k).map
      (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left
    let b := e.inv ≫ pullback.fst (pullback.snd f k) g
    let bi := fun i ↦ (ei i).inv ≫ pullback.fst (pullback.snd (fi i) k) g
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
    ∀ (hr : ∀ i, j i ≫ b = bi i ≫ jW i), ∀ i,
      (derivedPullback (j i)).map
          (picardResidueNormalizationCoefficient f L W k g t e hefst τ) ≫
        (Modules.canonicalSinglePullbackMap (j i)
            (SheafOfModules.unit Xs.ringCatSheaf) ≫
          (DerivedCategory.singleFunctor _ 0).map
            (Modules.pullbackObjUnitIso (j i)).hom) =
      (relativeMVComp (j i) b).hom.app K ≫
        eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K) (hr i)) ≫
        (relativeMVComp (bi i) (jW i)).inv.app K ≫
        (derivedPullback (bi i)).map
          (Modules.canonicalSinglePullbackMap (jW i) M ≫
            (DerivedCategory.singleFunctor _ 0).map
              (picardResidueCoefficientIso f (fi i) (ui i) (hui i) L W k).hom) ≫
        picardResidueNormalizationCoefficient (fi i) ((Modules.tensorPullback (ui i)).obj L)
          W k g t (ei i) (heifst i) (τi i) := by
  set_option backward.defeqAttrib.useBackward true in
  classical
  intro _E _Ei Xs Xis _A _Ai j τi jW b bi M K hr i
  let Mi := (Modules.tensorPullback (pullback.fst (fi i) k)).obj
    ((Modules.tensorPullback (ui i)).obj L)
  let α := picardResidueCoefficientIso f (fi i) (ui i) (hui i) L W k
  have hb : b ≫ pullback.fst f k = pullback.fst f t := by
    dsimp only [b]
    rw [Category.assoc, ← hefst, e.inv_hom_id_assoc]
  have hbi : bi i ≫ pullback.fst (fi i) k = pullback.fst (fi i) t := by
    dsimp only [bi]
    rw [Category.assoc, ← heifst, (ei i).inv_hom_id_assoc]
  let c := Modules.tensorCoefficientComparison
    (pullback.fst f k) (pullback.fst f t) b hb L ≪≫ τ
  let ci := Modules.tensorCoefficientComparison
    (pullback.fst (fi i) k) (pullback.fst (fi i) t) (bi i) hbi
      ((Modules.tensorPullback (ui i)).obj L) ≪≫ τi i
  let H := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback (fi i) t).toRingedSpace)) 0
  let C := (Modules.pullbackComp (bi i) (jW i)).app M ≪≫
    (Modules.pullbackCongr (hr i).symm).app M ≪≫
    ((Modules.pullbackComp (j i) b).app M).symm
  have ho := picard_ordinary_residue_coefficient_square
    f Xi fi ui hui L W k g t r h e hefst hesnd ei heifst heisnd τ hr i
  dsimp only at ho
  simp only [← picard_tensor_ordinary_coefficient_triangle] at ho
  have ho' := ho
  have hs := Modules.canonicalSinglePullbackSquare (jW i) b (bi i) (j i)
    (hr i).symm M Mi α.hom
  have hn := Modules.residue_singlePullback_naturality (j i) c.hom
  have hs' := congrArg (fun z ↦ z ≫ H.map ci.hom) hs
  have hoS := congrArg (fun z ↦
    (derivedPullback (j i)).map (Modules.canonicalSinglePullbackMap b M) ≫
      Modules.canonicalSinglePullbackMap (j i) ((Modules.pullback b).obj M) ≫ H.map z) ho'
  change (derivedPullback (j i)).map
      (Modules.canonicalSinglePullbackMap b M ≫ (DerivedCategory.singleFunctor _ 0).map c.hom) ≫
      (Modules.canonicalSinglePullbackMap (j i)
          (SheafOfModules.unit Xs.ringCatSheaf) ≫
        H.map (Modules.pullbackObjUnitIso (j i)).hom) = _
  simp only [Functor.map_comp, Category.assoc]
  have hstart := congrArg (fun z ↦
    (derivedPullback (j i)).map (Modules.canonicalSinglePullbackMap b M) ≫
      z ≫ H.map (Modules.pullbackObjUnitIso (j i)).hom) hn
  simp only [Category.assoc] at hstart
  refine hstart.trans ?_
  simp only [Functor.map_comp, Category.assoc] at hoS hs'
  exact hoS.trans hs'.symm

end AlgebraicGeometry.Scheme
