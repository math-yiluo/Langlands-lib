/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
public import WeilConjectures.AlgebraicGeometry.TensorCoefficientComparison

/-! # PicardResidueNormalizationMap

## References

* Stacks Project, Tags 0096 and 01F7
* Stacks Project, Tags 0096 and 0D5S
* Stacks Project, Tags 0096 and 06YJ
* Stacks Project, Tags 08HY, 0A1D and 0096
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The ordinary coefficient comparison for an arrow `u` over a base: the pullback along the
base change of `u` of the tensor pullback of `L` to `X ×_S W` is the tensor pullback to
`X' ×_S W` of the tensor pullback of `L` along `u`. -/
noncomputable def picardResidueCoefficientIso
    {X X' S : Scheme.{v}} (f : X ⟶ S) (f' : X' ⟶ S)
    (u : X' ⟶ X) (hu : u ≫ f = f') (L : X.Modules)
    (W : Scheme.{v}) (k : W ⟶ S) :
    let j := ((Over.pullback k).map
      (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left
    (Modules.pullback j).obj ((Modules.tensorPullback (pullback.fst f k)).obj L) ≅
      (Modules.tensorPullback (pullback.fst f' k)).obj
        ((Modules.tensorPullback u).obj L) := by
  classical
  let j := ((Over.pullback k).map
    (Over.homMk (U := Over.mk f') (V := Over.mk f) u hu)).left
  let t (Y Z : Scheme.{v}) (g : Y ⟶ Z) :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
  exact (Modules.pullback j).mapIso ((t _ _ (pullback.fst f k)).app L) ≪≫
    (Modules.pullbackComp j (pullback.fst f k)).app L ≪≫
    (Modules.pullbackCongr (picardCoefficientBaseMap_fst f f' u hu W k)).app L ≪≫
    ((Modules.pullbackComp (pullback.fst f' k) u).app L).symm ≪≫
    (Modules.pullback (pullback.fst f' k)).mapIso ((t _ _ u).app L).symm ≪≫
    ((t _ _ (pullback.fst f' k)).app ((Modules.tensorPullback u).obj L)).symm

/-- The ordinary-pullback form of a tensor coefficient triangle. -/
noncomputable def picardOrdinaryCoefficientTriangle
    {A B X : Scheme.{v}} (q : A ⟶ X) (q' : B ⟶ X) (b : B ⟶ A)
    (hb : b ≫ q = q') (L : X.Modules) :
    (Modules.pullback b).obj ((Modules.tensorPullback q).obj L) ≅
      (Modules.tensorPullback q').obj L := by
  classical
  let t (Y Z : Scheme.{v}) (a : Y ⟶ Z) :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction a)
  exact (Modules.pullback b).mapIso ((t _ _ q).app L) ≪≫
    (Modules.pullbackComp b q).app L ≪≫ (Modules.pullbackCongr hb).app L ≪≫
    ((t _ _ q').app L).symm

/-- The coefficient part of the explicit residue normalization: the canonical single-pullback
map followed by the single image of the coefficient triangle isomorphism composed with the
given trivialization. -/
noncomputable def picardResidueNormalizationCoefficient
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S) (L : X.Modules)
    (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (g : T ⟶ W) (t : T' ⟶ S)
    (e : pullback (pullback.snd f k) g ≅ pullback f t)
    (hefst : e.hom ≫ pullback.fst f t =
      pullback.fst (pullback.snd f k) g ≫ pullback.fst f k)
    (τ : (Modules.tensorPullback (pullback.fst f t)).obj L ≅
      SheafOfModules.unit (pullback f t).ringCatSheaf) :
    let b := e.inv ≫ pullback.fst (pullback.snd f k) g
    (derivedPullback b).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L)) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f t).toRingedSpace)) 0).obj
          (SheafOfModules.unit (pullback f t).ringCatSheaf) := by
  classical
  let b := e.inv ≫ pullback.fst (pullback.snd f k) g
  have hb : b ≫ pullback.fst f k = pullback.fst f t := by
    dsimp only [b]
    rw [Category.assoc, ← hefst, e.inv_hom_id_assoc]
  let c := Modules.tensorCoefficientComparison
    (pullback.fst f k) (pullback.fst f t) b hb L ≪≫ τ
  exact Modules.canonicalSinglePullbackMap b
      ((Modules.tensorPullback (pullback.fst f k)).obj L) ≫
    (DerivedCategory.singleFunctor _ 0).map c.hom

/-- The explicit residue normalization morphism: the composite of the base-change mate of the
square with the identified fibre as apex, the canonical single map, the tensor coefficient
comparison for the first projection, and the single image of the trivialization. -/
noncomputable def picardResidueNormalizationMap
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S) (L : X.Modules)
    (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (g : T ⟶ W) (t : T' ⟶ S) (r : T ≅ T')
    (e : pullback (pullback.snd f k) g ≅ pullback f t)
    (hefst : e.hom ≫ pullback.fst f t =
      pullback.fst (pullback.snd f k) g ≫ pullback.fst f k)
    (hesnd : e.hom ≫ pullback.snd f t ≫ r.inv = pullback.snd (pullback.snd f k) g)
    (τ : (Modules.tensorPullback (pullback.fst f t)).obj L ≅
      SheafOfModules.unit (pullback f t).ringCatSheaf) :
    (derivedPullback g).obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) ⟶
    (schemeDerivedDirectImage (pullback.snd f t ≫ r.inv)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f t).toRingedSpace)) 0).obj
          (SheafOfModules.unit (pullback f t).ringCatSheaf)) := by
  classical
  let b := e.inv ≫ pullback.fst (pullback.snd f k) g
  let q := pullback.snd f t ≫ r.inv
  have hs : e.inv ≫ pullback.snd (pullback.snd f k) g = q := by
    rw [← hesnd, e.inv_hom_id_assoc]
  have hw : b ≫ pullback.snd f k = q ≫ g := by
    dsimp only [b]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  exact schemeDerivedBaseChangeMap (pullback.snd f k) q g b hw
      ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (schemeDerivedDirectImage q).map
      (picardResidueNormalizationCoefficient f L W k g t e hefst τ)

end AlgebraicGeometry.Scheme
