/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.LimitDerivedDirectImageExchange
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-! # Derived direct-image exchange along a limit of smooth schemes

Source: Stacks Project, Tag 0F09, specialized to a field base and a degree-zero sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem isIso_abelian_derivedExchange_single_of_smooth
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Spec (.of k)) [Smooth g]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback f g).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let R := ULift.{u + 1} (ZMod n)
  let U := moduleAbelianForget R X
  obtain ⟨M, ⟨eF⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X n F hF
  have hn₀ : n ≠ 0 := fun h ↦ hn (by simp [h])
  have hnR : (n : R) = 0 := by
    exact ULift.ringEquiv.injective (by simp)
  have hnS : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    have hu : IsUnit (n : k) := isUnit_iff_ne_zero.mpr hn
    simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) M :=
    Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero R n hn₀ hnR hnS M
  let sq := IsPullback.of_hasPullback f g
  let P := (DerivedCategory.Plus.singleFunctor _ 0).obj M
  have hM := isIso_baseChange_app_singleFunctor_obj_of_smooth R g sq M
  rw [baseChange_eq_derivedBaseChangeMapPlus] at hM
  have : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} R) sq.toCommSq).app P) := hM
  have hcomp := moduleAbelianDerivedExchange_compatibility R sq.toCommSq P
  have hi : IsIso ((moduleAbelianDerivedExchangeSourceIso R f g P).hom ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        (U.mapDerivedCategoryPlus.obj P)) := by
    rw [← hcomp]
    infer_instance
  have hi' : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      (U.mapDerivedCategoryPlus.obj P)) :=
    IsIso.of_isIso_comp_left (moduleAbelianDerivedExchangeSourceIso R f g P).hom _
  let e := (U.mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso eF
  exact (NatTrans.isIso_app_iff_of_iso
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) e).1 hi'

/-- Relative derived exchange passes to a cofiltered limit of smooth qcqs schemes
with affine transitions, for coefficients killed by an integer invertible in the field.
Source: Stacks Project, Lemma 59.89.3, Tag 0F09; limit comparison Tag 0EZT.
(blueprint: lem-sc-smooth-limit-derived-direct-image-exchange)

Proof: For each stage, form X_i = X times_{Spec k} D_i. Smooth base change identifies
the inverse image of Rf_* F with Rf_{i,*} of the inverse image of F. The n-torsion
hypothesis on F gives the torsion hypothesis at every geometric stalk, and hn makes
n invertible on every stage. The X_i have affine transition maps and limit
X times_{Spec k} c.pt, since base change preserves limits. In any fixed degree q,
the higher-direct-image limit comparison (Tag 0EZT) identifies the two sides of the
limit exchange map with filtered colimits of the pulled-back stage higher direct
images. Every stage exchange map is an isomorphism by smooth base change, hence the
filtered colimit map is an isomorphism. Exact inverse image commutes with homology.
The sheaf F in degree zero is bounded below; applying the single-complex derived
functor comparison identifies these degreewise maps with the homology maps of the
derived exchange. A morphism in the derived category which induces isomorphisms in
every degree is invertible. Finally exact inverse image commutes with degree-zero
single complexes. This gives the displayed isomorphism. The cofiltered index is
nonempty. Zero coefficients or the empty source give zero objects; n = 1 forces
zero coefficients, and n = 0 is excluded by hn. -/
theorem nonempty_smoothLimit_derivedDirectImage_single_iso
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, Smooth (D.obj i).hom]
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0) :
    Nonempty
      (((upperStar AddCommGrpCat.{u + 1} c.pt.hom).mapDerivedCategory).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
        (lowerStar AddCommGrpCat.{u + 1} (pullback.snd f c.pt.hom)).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} (pullback.fst f c.pt.hom)).obj F))) := by
  refine nonempty_limit_derivedDirectImage_single_iso D c hc f F ?_
  intro i
  exact isIso_abelian_derivedExchange_single_of_smooth f (D.obj i).hom n hn F hF

end AlgebraicGeometry.Etale
