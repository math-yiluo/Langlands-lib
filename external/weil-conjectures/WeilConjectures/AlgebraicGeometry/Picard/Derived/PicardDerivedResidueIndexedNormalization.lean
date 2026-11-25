/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueNormalizationMap
import WeilConjectures.AlgebraicGeometry.Derived.DerivedBaseChangeSourceTransport

/-! # PicardDerivedResidueIndexedNormalization

## References

* Stacks Project, Tags 0096, 06YJ, 0A1D, 08HY, 0D5S and 01F7
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem image_map_transport
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {Y B : Scheme.{v}} (p p' : Y ⟶ B) (hp : p = p')
    {K K' : schemeDerivedCategory Y} (a : K ⟶ K') :
    (schemeDerivedDirectImage p).map a ≫
        eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj K') hp) =
      eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj K) hp) ≫
        (schemeDerivedDirectImage p').map a := by
  subst p'
  simp

private theorem baseChange_transport
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {Y B P A : Scheme.{v}} (p p' : Y ⟶ B) (hp : p = p')
    (g : A ⟶ B) (r : P ⟶ Y) (s : P ⟶ A)
    (h : r ≫ p = s ≫ g) (h' : r ≫ p' = s ≫ g)
    (K : schemeDerivedCategory Y) :
    (derivedPullback g).map
        (eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj K) hp)) ≫
        schemeDerivedBaseChangeMap p' s g r h' K =
      schemeDerivedBaseChangeMap p s g r h K := by
  subst p'
  simp

/-- The explicit normalization maps respect coefficient arrows. -/
theorem picardResidueNormalizationMap_naturality_of_coefficientSquare
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
    (_h : g ≫ k = r.hom ≫ t)
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
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings Xs.toRingedSpace)) 0).obj
        (SheafOfModules.unit Xs.ringCatSheaf)
    let Ai := fun i ↦ (DerivedCategory.singleFunctor
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
    ∀ (hr : ∀ i, j i ≫ b = bi i ≫ jW i),
    (∀ i,
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
          W k g t (ei i) (heifst i) (τi i)) →
    ∀ (hj : ∀ i, j i ≫ (pullback.snd f t ≫ r.inv) =
      pullback.snd (fi i) t ≫ r.inv), ∀ i,
      (derivedPullback g).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫
        picardResidueNormalizationMap (fi i) ((Modules.tensorPullback (ui i)).obj L)
          W k g t r (ei i) (heifst i) (heisnd i) (τi i) =
      picardResidueNormalizationMap f L W k g t r e hefst hesnd τ ≫
        relativeMVUnit (j i) (pullback.snd f t ≫ r.inv) A ≫
        (schemeDerivedDirectImage (j i ≫ (pullback.snd f t ≫ r.inv))).map
          (Modules.canonicalSinglePullbackMap (j i)
              (SheafOfModules.unit Xs.ringCatSheaf) ≫
            (DerivedCategory.singleFunctor _ 0).map
              (Modules.pullbackObjUnitIso (j i)).hom) ≫
        eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj (Ai i)) (hj i)) := by
  classical
  intro _E _Ei Xs Xis A Ai j τi jW b bi M K hr hc hj i
  let p := pullback.snd f k
  let pi := pullback.snd (fi i) k
  let q := pullback.snd f t ≫ r.inv
  let qi := pullback.snd (fi i) t ≫ r.inv
  let Mi := (Modules.tensorPullback (pullback.fst (fi i) k)).obj
    ((Modules.tensorPullback (ui i)).obj L)
  let Ki := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj Mi
  let a := Modules.canonicalSinglePullbackMap (jW i) M ≫
    (DerivedCategory.singleFunctor _ 0).map
      (picardResidueCoefficientIso f (fi i) (ui i) (hui i) L W k).hom
  let c := picardResidueNormalizationCoefficient f L W k g t e hefst τ
  let ci := picardResidueNormalizationCoefficient (fi i)
    ((Modules.tensorPullback (ui i)).obj L) W k g t (ei i) (heifst i) (τi i)
  let d := Modules.canonicalSinglePullbackMap (j i)
      (SheafOfModules.unit Xs.ringCatSheaf) ≫
    (DerivedCategory.singleFunctor _ 0).map (Modules.pullbackObjUnitIso (j i)).hom
  have hp : jW i ≫ p = pi := picardCoefficientBaseMap_snd f (fi i) (ui i) (hui i) W k
  have hw : b ≫ p = q ≫ g := by
    dsimp only [b, p, q]
    rw [Category.assoc, pullback.condition, ← hesnd]
    simp only [Category.assoc, e.inv_hom_id_assoc]
  have hwi : bi i ≫ pi = qi ≫ g := by
    dsimp only [bi, pi, qi]
    rw [Category.assoc, pullback.condition, ← heisnd]
    simp only [Category.assoc, (ei i).inv_hom_id_assoc]
  have hwi' : bi i ≫ (jW i ≫ p) = qi ≫ g := by rw [hp]; exact hwi
  have ht := derivedBaseChange_source_transport p g (jW i) b q (bi i) qi (j i)
    hw hwi' (hr i) (hj i) K Ki A (Ai i) a c ci d (hc i)
  let e0 := relativeMVUnit (jW i) p K ≫ (schemeDerivedDirectImage (jW i ≫ p)).map a
  let F := relativeMVUnit (j i) q A ≫
    eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj
      ((derivedPullback (j i)).obj A)) (hj i)) ≫
    (schemeDerivedDirectImage qi).map d
  have ht' : schemeDerivedBaseChangeMap p q g b hw K ≫
      (schemeDerivedDirectImage q).map c ≫ F =
    (derivedPullback g).map e0 ≫ schemeDerivedBaseChangeMap (jW i ≫ p) qi g
      (bi i) hwi' Ki ≫ (schemeDerivedDirectImage qi).map ci := by
    simpa only [e0, F, relativeMVUnit, Category.assoc] using ht
  have he : picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k =
      e0 ≫ eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj Ki) hp) := by
    simp only [picardDerivedCoefficientMap, picardResidueCoefficientIso,
      e0, a, p, K, M, Ki, Mi, jW, Category.assoc]
  have hb := baseChange_transport (jW i ≫ p) pi hp g (bi i) qi hwi' hwi Ki
  have hF : F = relativeMVUnit (j i) q A ≫
      (schemeDerivedDirectImage (j i ≫ q)).map d ≫
      eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj (Ai i)) (hj i)) := by
    simpa only [F, Category.assoc] using
      congrArg (fun z ↦ relativeMVUnit (j i) q A ≫ z)
        (image_map_transport (j i ≫ q) qi (hj i) d).symm
  change (derivedPullback g).map
      (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫
      (schemeDerivedBaseChangeMap pi qi g (bi i) hwi Ki ≫
        (schemeDerivedDirectImage qi).map ci) =
    (schemeDerivedBaseChangeMap p q g b hw K ≫
      (schemeDerivedDirectImage q).map c) ≫
      relativeMVUnit (j i) q A ≫
        (schemeDerivedDirectImage (j i ≫ q)).map d ≫
        eqToHom (congrArg (fun z ↦ (schemeDerivedDirectImage z).obj (Ai i)) (hj i))
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hb, ← ht', hF]

end AlgebraicGeometry.Scheme
