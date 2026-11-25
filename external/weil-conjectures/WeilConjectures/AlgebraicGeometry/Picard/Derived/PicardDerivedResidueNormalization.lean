/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedResidueSourceNormalization
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedResidueIndexedNormalization
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueCoefficientSquare

/-! # Normalize derived direct images over an identified change of base

## References

* Stacks Project, Tag 0A1D, relatively flat derived base change
* Tags 08HY and 0D5S, the base-change mate and pullback composition
* Tag 01F7, functoriality under the residue-point and fibre isomorphisms
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Proper flat base change over identified bases and one trivialization normalize
coefficient arrows in the derived category, before homology or sections is applied. -/
theorem picard_derived_residue_normalization
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
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
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
    ∃ (a : (derivedPullback g).obj E ≅
        (schemeDerivedDirectImage (pullback.snd f t ≫ r.inv)).obj A)
      (ai : ∀ i, (derivedPullback g).obj (Ei i) ≅
        (schemeDerivedDirectImage
          (pullback.snd (fi i) t ≫ r.inv)).obj (Ai i)),
      let q := pullback.snd f t ≫ r.inv
      let qi := fun i ↦ pullback.snd (fi i) t ≫ r.inv
      ∃ hj : ∀ i, j i ≫ q = qi i,
        ∀ i, (derivedPullback g).map
            (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (ai i).hom =
          a.hom ≫ relativeMVUnit (j i) q A ≫
            (schemeDerivedDirectImage (j i ≫ q)).map
              (Modules.canonicalSinglePullbackMap (j i)
                  (SheafOfModules.unit Xs.ringCatSheaf) ≫
                (DerivedCategory.singleFunctor _ 0).map
                  (Modules.pullbackObjUnitIso (j i)).hom) ≫
            eqToHom (congrArg (fun t ↦ (schemeDerivedDirectImage t).obj (Ai i)) (hj i)) := by
  classical
  dsimp only
  let j := fun i ↦ ((Over.pullback t).map
    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left
  let τi := fun i ↦
    (picardResidueCoefficientIso f (fi i) (ui i) (hui i) L T' t).symm ≪≫
      (Modules.pullback (j i)).mapIso τ ≪≫ Modules.pullbackObjUnitIso (j i)
  have hj : ∀ i, j i ≫ (pullback.snd f t ≫ r.inv) =
      pullback.snd (fi i) t ≫ r.inv := by
    intro i
    rw [← Category.assoc, picardCoefficientBaseMap_snd]
  let := isIso_picardResidueNormalizationMap f L W k g t r e hefst hesnd τ
  have (i : Fin n) : Modules.IsInvertible ((Modules.tensorPullback (ui i)).obj L) := by
    let c := (Classical.choose (Modules.exists_tensorPullbackAdjunction (ui i))).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction (ui i))
    exact Modules.IsInvertible.of_iso (c.app L).symm
  let (i : Fin n) := isIso_picardResidueNormalizationMap (fi i)
    ((Modules.tensorPullback (ui i)).obj L) W k g t r (ei i) (heifst i) (heisnd i) (τi i)
  refine ⟨asIso (picardResidueNormalizationMap f L W k g t r e hefst hesnd τ),
    (fun i ↦ asIso (picardResidueNormalizationMap (fi i)
      ((Modules.tensorPullback (ui i)).obj L) W k g t r
        (ei i) (heifst i) (heisnd i) (τi i))), hj, ?_⟩
  have hr : ∀ i, j i ≫ (e.inv ≫ pullback.fst (pullback.snd f k) g) =
      ((ei i).inv ≫ pullback.fst (pullback.snd (fi i) k) g) ≫
        (((Over.pullback k).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) := by
    intro i
    apply pullback.hom_ext
    · simp only [Category.assoc, picardCoefficientBaseMap_fst]
      have he : e.inv ≫ pullback.fst (pullback.snd f k) g ≫ pullback.fst f k =
          pullback.fst f t := by rw [← hefst, e.inv_hom_id_assoc]
      have hei : (ei i).inv ≫ pullback.fst (pullback.snd (fi i) k) g ≫
          pullback.fst (fi i) k = pullback.fst (fi i) t := by
        rw [← heifst, (ei i).inv_hom_id_assoc]
      rw [he, picardCoefficientBaseMap_fst]
      simpa only [Category.assoc] using
        (congrArg (fun z ↦ z ≫ ui i) hei).symm
    · have he : e.inv ≫ pullback.snd (pullback.snd f k) g =
          pullback.snd f t ≫ r.inv := by
        rw [← hesnd, e.inv_hom_id_assoc]
      have hei : (ei i).inv ≫ pullback.snd (pullback.snd (fi i) k) g =
          pullback.snd (fi i) t ≫ r.inv := by
        rw [← heisnd, (ei i).inv_hom_id_assoc]
      have he' := congrArg (fun z ↦ z ≫ g) he
      have hei' := congrArg (fun z ↦ z ≫ g) hei
      simp only [Category.assoc] at he' hei'
      simp only [Category.assoc, picardCoefficientBaseMap_snd]
      rw [pullback.condition, pullback.condition, he', hei']
      simpa only [← Category.assoc] using
        congrArg (fun z ↦ (z ≫ r.inv) ≫ g)
          (picardCoefficientBaseMap_snd f (fi i) (ui i) (hui i) T' t)
  have hcoeff := picardResidueCoefficientSquare
    f Xi fi ui hui L W k g t r h e hefst hesnd ei heifst heisnd τ hr
  exact picardResidueNormalizationMap_naturality_of_coefficientSquare
    f Xi fi ui hui L W k g t r h e hefst hesnd ei heifst heisnd τ hr hcoeff hj

end AlgebraicGeometry.Scheme
