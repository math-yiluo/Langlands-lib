/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology

/-! # Coherence of restricted fixed-coefficient single complexes

Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of fixed coefficients.
(blueprint: def-sbc-restricted-over-single-data).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar upperStarComp upperStarId

/-- Actual fibre products and their canonical transition arrows.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: def-sbc-restricted-over-single-data). -/
@[implicit_reducible]
noncomputable def restrictedOverDiagram {W S : Scheme.{u}} (k : W ⟶ S)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (U : S.Etale) :
    I ⥤ Scheme.{u} where
  obj i := pullback U.hom ((D.obj i).hom ≫ k)
  map f := rawAffineRestrictedMap (D.map f).left ((D.obj _).hom ≫ k)
    ((D.obj _).hom ≫ k) (by rw [← Category.assoc, Over.w]) U
  map_id i := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap]
  map_comp f g := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap, Category.assoc]

/-- The fibre-product cone, constructed without choosing a limit witness.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: def-sbc-restricted-over-single-data). -/
@[implicit_reducible]
noncomputable def restrictedOverCone {W S : Scheme.{u}} (k : W ⟶ S)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Cone (restrictedOverDiagram k D U) where
  pt := pullback U.hom (c.pt.hom ≫ k)
  π :=
    { app := fun i ↦ rawAffineRestrictedMap (c.π.app i).left ((D.obj i).hom ≫ k)
        (c.pt.hom ≫ k) (by rw [← Category.assoc, Over.w]; rfl) U
      naturality := by
        intro i j f
        apply pullback.hom_ext <;>
          simp [restrictedOverDiagram, rawAffineRestrictedMap, Category.assoc,
            ← Over.comp_left, c.w f] }

/-- A fixed sheaf restricted to an actual fibre product, placed in degree zero.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: def-sbc-restricted-over-single-data). -/
@[implicit_reducible]
noncomputable def restrictedOverSingle {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (A : Over W) (U : S.Etale) :
    CochainComplex (Sheaf (pullback U.hom (A.hom ≫ k)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (A.hom ≫ k))).obj
      ((upperStar AddCommGrpCat.{u + 1} A.hom).obj F))

/-- The explicit isomorphism for a triangle, including the single-functor comparison.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: def-sbc-restricted-over-single-data). -/
noncomputable def restrictedOverSingleIso {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    ((upperStar AddCommGrpCat.{u + 1}
      (rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictedOverSingle k F B U) ≅
      restrictedOverSingle k F A U := by
  let w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k := by rw [← Category.assoc, Over.w]
  let a := rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k) w U
  let r := pullback.snd U.hom (B.hom ≫ k)
  let r' := pullback.snd U.hom (A.hom ≫ k)
  let R := (upperStar AddCommGrpCat.{u + 1} B.hom).obj F
  have hw : r' ≫ f.left = a ≫ r := by simp [a, r, r', rawAffineRestrictedMap]
  let e := ((upperStar AddCommGrpCat.{u + 1} a).mapCochainComplexSingleFunctor 0).app
    ((upperStar AddCommGrpCat.{u + 1} r).obj R) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso
      (((upperStarComp AddCommGrpCat.{u + 1} a r).app R).symm ≪≫
        (upperStarComp AddCommGrpCat.{u + 1} r' f.left (a ≫ r) hw.symm).app R ≪≫
        (upperStar AddCommGrpCat.{u + 1} r').mapIso
          (((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).app F).symm))
  let h := ((upperStar AddCommGrpCat.{u + 1} a).mapCochainComplexSingleFunctor 0).hom.app
    ((upperStar AddCommGrpCat.{u + 1} r).obj R) ≫
    (CochainComplex.singleFunctor _ 0).map
      (rawAffineRestrictedCoefficient f.left (B.hom ≫ k) (A.hom ≫ k) w
        R ((upperStar AddCommGrpCat.{u + 1} A.hom).obj F)
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app F) U)
  set_option backward.isDefEq.respectTransparency true in
  have : IsIso h := by
    change IsIso e.hom
    infer_instance
  exact asIso h

/-- The constant complex on the limiting fibre product.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: def-sbc-restricted-over-single-data). -/
@[implicit_reducible]
noncomputable def restrictedOverSingleG {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Iᵒᵖ ⥤ CochainComplex (Sheaf (pullback U.hom (c.pt.hom ≫ k)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ :=
  (Functor.const Iᵒᵖ).obj (restrictedOverSingle k F c.pt U)

/-- The cone comparison is the inverse of the explicitly constructed leg isomorphism.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: def-sbc-restricted-over-single-data). -/
@[implicit_reducible]
noncomputable def restrictedOverSingleConeIso {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale)
    (i : I) :
    (restrictedOverSingleG k F D c U).obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1}
        ((restrictedOverCone k D c U).π.app i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (restrictedOverSingle k F (D.obj i) U) :=
  (restrictedOverSingleIso k F (A := c.pt) (B := D.obj i) (c.π.app i) U).symm

end AlgebraicGeometry.Etale
