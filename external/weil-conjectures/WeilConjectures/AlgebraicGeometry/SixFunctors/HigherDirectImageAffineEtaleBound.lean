/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionAbelianDirectImageVanishing

/-!
# Higher direct image bounds from affine etale objects

## References

* Stacks 072W
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem module_vanishing {X Y : Scheme.{u}} (g : X ⟶ Y) (c : ℕ)
    (hc : ∀ {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W],
      Scheme.HasTorsionEtaleCohomologicalDimensionLE (pullback w g) c)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hM : ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj M).IsTorsion)
    (q : ℤ) (hq : (c : ℤ) < q) :
    IsZero (Etale.higherDirectImage (ULift.{u + 1} ℤ) g q M) := by
  let Λ := ULift.{u + 1} ℤ
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
  refine Etale.isZero_higherDirectImage_of_forall_isAffine g _ M fun W hW ↦ ?_
  have : IsAffine W.left := hW
  have : IsAffine ((𝟭 Scheme.{u}).obj W.left) := hW
  have : AlgebraicGeometry.Etale W.hom := W.prop
  let V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj W
  have : AlgebraicGeometry.Etale V.hom := V.prop
  let Φ := sheafCompose V.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let N := Φ.obj ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj M)
  have hN : N.IsTorsion := Sheaf.IsTorsion.of_iso
    (asIso ((Etale.upperStarForget₂ Λ V.hom).app M))
    (Etale.isTorsion_upperStar V.hom hM)
  have hsub := hc W.hom N hN (n + 1) (by omega)
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso V.left (n + 1)
  have : Subsingleton ((DerivedCategory.singleFunctor _ 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} V.left ((n + 1 : ℕ) : ℤ)).obj N) := hsub
  have hH : Subsingleton (Sheaf.H N (n + 1)) :=
    (e.app N).addCommGroupIsoToAddEquiv.injective.subsingleton
  have : Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ X).obj V) M (n + 1)) :=
    Etale.subsingleton_ext_freeSheaf_of_subsingleton_H_of_acyclic V M n
      (fun I _ m ↦ Etale.subsingleton_H_forget₂_uliftInt_of_injective I m) hH
  exact ((DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1}
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj ((Etale.freeSheaf Λ Y).obj W))
      M (n + 1)).trans
    (Abelian.Ext.precompAddEquiv (Etale.upperStarFreeSheafIso Λ g W) M (n + 1)).symm.toEquiv
    ).subsingleton

/-- A bound on the absolute torsion cohomology of inverse images of affine etale objects
bounds higher direct images. No finiteness assumption on the morphism is needed. -/
theorem isZero_higherDirectImage_of_affineEtale_cd {X Y : Scheme.{u}} (g : X ⟶ Y)
    (c : ℕ)
    (hc : ∀ {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W],
      Scheme.HasTorsionEtaleCohomologicalDimensionLE (pullback w g) c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℤ) (hq : (c : ℤ) < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let ΦX := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let ΦY := sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let M := ΦX.asEquivalence.inverse.obj F
  let e : ΦX.obj M ≅ F := ΦX.asEquivalence.counitIso.app F
  have hM : (ΦX.obj M).IsTorsion := Sheaf.IsTorsion.of_iso e.symm hF
  have hz := ΦY.map_isZero (module_vanishing g c hc M hM q hq)
  let eH := (ΦY.mapDerivedCategoryPlusHomologyFunctorIso q).app
    ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) g).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M))
  let eR := (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (asIso ((rightDerivedLowerStarForget₂ g).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)))
  let eS := (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g).mapIso
      ((ΦX.mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso e))
  exact hz.of_iso (eH ≪≫ eR ≪≫ eS).symm

end AlgebraicGeometry.Etale
