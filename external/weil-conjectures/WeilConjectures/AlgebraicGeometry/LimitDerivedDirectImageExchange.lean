/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.LimitHigherDirectImageExchange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Continuity of relative exchange under affine inverse limits

Source: Stacks Project, Tag 0EZT, second assertion, and Tag 0EYM.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Derived exchange for an abelian sheaf passes from the stages to their inverse limit.
No smoothness or invertibility hypothesis enters this continuity step.
Source: Stacks Project, Lemma 59.86.3, Tag 0EZT, second assertion, and Tag 0EYM.
(blueprint: lem-sc-limit-derived-direct-image-exchange)

Proof: Replace the small cofiltered category by a cofinal directed inverse system;
this preserves its limit and the corresponding filtered colimits of sheaves.
Form the inverse system of cartesian squares by pulling f back to D_i.
The left base and the original source are constant systems, and the new bases have
affine transitions. Their pulled-back sources have affine transitions and limit
X times_{Spec k} c.pt. The coefficients are the constant system with value F;
their filtered colimit identifies with F since the index is nonempty and connected. For each
q >= 0, the given derived exchange isomorphisms imply isomorphisms of q-th
cohomology sheaves at every stage. Higher direct images commute with the affine
inverse limits (Tag 0EYM), so the limit base-change map in degree q is the filtered
colimit of these stage maps (Tag 0EZT). Thus it is an isomorphism. Negative-degree
cohomology vanishes, since F lies in degree zero and the total right derived direct
image is left t-exact; exact inverse image preserves this property. Consequently
the derived exchange induces isomorphisms in every degree and is invertible.
Use the compatibility of the bounded-below and total right derived functors to
read this in the total derived category. Exact inverse image commutes with single
complexes, giving the displayed target. All maps here are the canonical exchange
maps, so their compatibility with transition maps follows from adjunction-unit
naturality. The empty source and zero coefficients give zero objects. -/
theorem nonempty_limit_derivedDirectImage_single_iso
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hstage : ∀ i, IsIso
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f (D.obj i).hom).toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    Nonempty
      (((upperStar AddCommGrpCat.{u + 1} c.pt.hom).mapDerivedCategory).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
        (lowerStar AddCommGrpCat.{u + 1} (pullback.snd f c.pt.hom)).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} (pullback.fst f c.pt.hom)).obj F))) := by
  let g := c.pt.hom
  let p := pullback.fst f g
  let f' := pullback.snd f g
  let U := upperStar AddCommGrpCat.{u + 1} g
  let V := upperStar AddCommGrpCat.{u + 1} p
  let L := lowerStar AddCommGrpCat.{u + 1} f
  let L' := lowerStar AddCommGrpCat.{u + 1} f'
  let P := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let α := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback f g).toCommSq).app P
  have hα : IsIso α := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro q
    by_cases hq : q < 0
    · have hz₁ : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
          (U.mapDerivedCategoryPlus.obj (L.rightDerivedFunctorPlus.obj P))) := by
        refine IsZero.of_iso ?_
          (U.mapDerivedCategoryPlusHomologyFunctorIso q |>.app _).symm
        exact U.map_isZero
          (L.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE P 0 hq)
      have : (V.mapDerivedCategoryPlus.obj P).IsGE 0 := by
        rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
        intro i hi
        refine IsZero.of_iso ?_
          (V.mapDerivedCategoryPlusHomologyFunctorIso i |>.app _).symm
        exact V.map_isZero (DerivedCategory.Plus.isZero_homology_of_isGE P 0 i hi)
      have hz₂ := L'.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        (V.mapDerivedCategoryPlus.obj P) 0 hq
      exact ⟨⟨0, hz₁.eq_of_src _ _, hz₂.eq_of_src _ _⟩⟩
    · have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      rw [← hqn]
      apply isIso_limit_homology_derivedBaseChangeMapPlus D c hc f F q.toNat
      intro i
      have := hstage i
      infer_instance
  let e := DerivedCategory.Plus.ι.mapIso (asIso α)
  exact ⟨U.mapDerivedCategory.mapIso (L.rightDerivedFunctorPlusCompatibility.app P).symm ≪≫
    e ≪≫ L'.rightDerivedFunctorPlusCompatibility.app (V.mapDerivedCategoryPlus.obj P) ≪≫
    L'.rightDerivedFunctor.mapIso
      (DerivedCategory.Plus.ι.mapIso ((V.mapDerivedCategoryPlusSingleFunctor 0).app F))⟩

end AlgebraicGeometry.Etale
