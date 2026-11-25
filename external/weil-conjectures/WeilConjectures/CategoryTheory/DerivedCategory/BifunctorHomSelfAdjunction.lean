/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomBidual
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# The derived hom into a fixed complex is self-adjoint on the right

Let `H : Cᵒᵖ ⥤ C ⥤ C` be a bifunctor with evaluation morphisms `ev a b : a ⟶ H(H(a, b), b)`
(`CochainComplex.BifunctorEvaluation`) satisfying the triangle identity
`ev (H(a, b)) b ≫ H(ev a b, b) = 𝟙` (`CochainComplex.BifunctorEvaluation.TriangleIdentity`), as
the biduality morphisms of an internal hom do. Then:

* the double-dual morphisms of hom complexes satisfy the same triangle identity
  (`CochainComplex.bifunctorHomBidual_comp_bifunctorHomMapLeft`);
* for a complex `I` such that precomposition with quasi-isomorphisms is a quasi-isomorphism of
  hom complexes into `I`, the derived hom `G = RHom_H(-, I)` is self-adjoint on the right,
  `G.rightOp ⊣ G`, with unit the double-dual transformation
  (`DerivedCategory.bifunctorRHomSelfAdjunction`).

In particular, whether the double-dual morphism is invertible at an object can be compared with
any other self-adjunction of an isomorphic functor (`Adjunction.isIso_unit_app_iff_of_iso`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCountableProducts C]
  {H : Cᵒᵖ ⥤ C ⥤ C} [∀ X, (H.obj X).Additive] [H.Additive]

/-- The triangle identity `ev (H(a, b)) b ≫ H(ev a b, b) = 𝟙` of an evaluation. -/
def BifunctorEvaluation.TriangleIdentity (E : BifunctorEvaluation H) : Prop :=
  ∀ a b : C, E.ev ((H.obj (op a)).obj b) b ≫ (H.map (E.ev a b).op).app b = 𝟙 _

/-- The double-dual morphisms of hom complexes satisfy the triangle identity. -/
lemma bifunctorHomBidual_comp_bifunctorHomMapLeft {E : BifunctorEvaluation H}
    (hE : E.TriangleIdentity) (K Y : CochainComplex C ℤ) :
    bifunctorHomBidual E (bifunctorHomObj H K Y) Y ≫
      bifunctorHomMapLeft (H := H) (Y := Y) (bifunctorHomBidual E K Y) = 𝟙 _ := by
  ext n m r h
  rw [HomologicalComplex.comp_f, assoc, bifunctorHomMapLeft_f_π, bifunctorHomBidual_f_π_assoc,
    HomologicalComplex.id_f, id_comp]
  simp only [bifunctorHomBidualComponent, Linear.units_smul_comp, assoc]
  rw [← NatTrans.comp_app, ← H.map_comp, ← op_comp, bifunctorHomBidual_f_π]
  simp only [bifunctorHomBidualComponent, Units.smul_def, op_zsmul, Functor.map_zsmul,
    NatTrans.app_zsmul, Preadditive.comp_zsmul, smul_smul, op_comp, CategoryTheory.Functor.map_comp,
    NatTrans.comp_app]
  rw [mul_comm m n, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
    reassoc_of% (E.naturality (bifunctorHomπ H K Y n m r (by omega)) (Y.X r)).symm, hE, comp_id]

end CochainComplex

namespace DerivedCategory

open CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
  [Abelian.HasKInjectiveResolutions C] [HasCountableProducts C]
  {H : Cᵒᵖ ⥤ C ⥤ C} [H.Additive] [∀ M, (H.obj M).Additive]
  (E : BifunctorEvaluation H) {I : CochainComplex C ℤ} (hI : PrecompQuasiIso H I)

/-- The composite `G ⟶ G`, `G(φ_X) ∘ φ_{G X}`, of the double-dual transformation `φ` of the
derived hom `G = RHom_H(-, I)`. -/
noncomputable def bifunctorRHomBidualTriangle :
    bifunctorRHomOfComplex H I ⟶ bifunctorRHomOfComplex H I where
  app X := (bifunctorRHomBidual E hI).app ((bifunctorRHomOfComplex H I).obj X) ≫
    (bifunctorRHomOfComplex H I).map ((bifunctorRHomBidual E hI).app X.unop).op
  naturality X Y f := by
    have h₁ := (bifunctorRHomBidual E hI).naturality ((bifunctorRHomOfComplex H I).map f)
    have h₂ := (bifunctorRHomBidual E hI).naturality f.unop
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.rightOp_obj, Functor.id_map,
      Functor.comp_map, Functor.rightOp_map] at h₁ h₂ ⊢
    rw [Quiver.Hom.op_unop] at h₂
    rw [reassoc_of% h₁, ← CategoryTheory.Functor.map_comp, ← op_comp, ← h₂, op_comp,
      Quiver.Hom.op_unop, CategoryTheory.Functor.map_comp, assoc]

variable {E} in
lemma bifunctorRHomBidualTriangle_eq_id (hE : E.TriangleIdentity) :
    bifunctorRHomBidualTriangle E hI = 𝟙 _ := by
  refine Localization.natTrans_ext Q.op (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
    fun K ↦ ?_
  induction K with | op K₀ => ?_
  have hK := bifunctorRHomBidual_app_Q_obj E hI K₀
  have hL := bifunctorRHomBidual_app_Q_obj E hI (bifunctorHomObj H K₀ I)
  have hn := (bifunctorRHomBidual E hI).naturality (bifunctorRHomOfComplexQObjIso H hI K₀).hom
  have hnat := bifunctorRHomOfComplexQObjIso_hom_naturality hI (bifunctorHomBidual E K₀ I)
  dsimp only [bifunctorRHomBidualAux, Functor.id_obj, Functor.comp_obj, Functor.rightOp_obj,
    Functor.id_map, Functor.comp_map, Functor.rightOp_map] at hK hL hn
  have c₁ : (bifunctorRHomOfComplex H I).map ((bifunctorRHomOfComplex H I).map
        (bifunctorRHomOfComplexQObjIso H hI K₀).hom.op).op ≫
      (bifunctorRHomOfComplex H I).map ((bifunctorRHomOfComplex H I).map
        (bifunctorRHomOfComplexQObjIso H hI K₀).inv.op).op = 𝟙 _ := by
    simp only [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
      CategoryTheory.Functor.map_id]
  have c₁' : (bifunctorRHomOfComplex H I).map ((bifunctorRHomOfComplex H I).map
        (bifunctorRHomOfComplexQObjIso H hI K₀).inv.op).op ≫
      (bifunctorRHomOfComplex H I).map ((bifunctorRHomOfComplex H I).map
        (bifunctorRHomOfComplexQObjIso H hI K₀).hom.op).op = 𝟙 _ := by
    simp only [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
      CategoryTheory.Functor.map_id]
  have c₂ : (bifunctorRHomOfComplex H I).map
        (bifunctorRHomOfComplexQObjIso H hI (bifunctorHomObj H K₀ I)).hom.op ≫
      (bifunctorRHomOfComplex H I).map
        (bifunctorRHomOfComplexQObjIso H hI (bifunctorHomObj H K₀ I)).inv.op = 𝟙 _ := by
    simp only [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
      CategoryTheory.Functor.map_id]
  have hGK : (bifunctorRHomBidual E hI).app
      ((bifunctorRHomOfComplex H I).obj (op (Q.obj K₀))) =
      (bifunctorRHomOfComplexQObjIso H hI K₀).hom ≫
        (bifunctorRHomBidual E hI).app (Q.obj (bifunctorHomObj H K₀ I)) ≫
          (bifunctorRHomOfComplex H I).map ((bifunctorRHomOfComplex H I).map
            (bifunctorRHomOfComplexQObjIso H hI K₀).inv.op).op := by
    rw [reassoc_of% hn, c₁, comp_id]
  change (bifunctorRHomBidual E hI).app ((bifunctorRHomOfComplex H I).obj (op (Q.obj K₀))) ≫
      (bifunctorRHomOfComplex H I).map ((bifunctorRHomBidual E hI).app (Q.obj K₀)).op = 𝟙 _
  rw [← cancel_mono (bifunctorRHomOfComplexQObjIso H hI K₀).hom, id_comp, hGK, hL, hK]
  simp only [op_comp, CategoryTheory.Functor.map_comp, assoc]
  rw [reassoc_of% c₁', reassoc_of% c₂, hnat, Iso.inv_hom_id_assoc, ← Q.map_comp,
    bifunctorHomBidual_comp_bifunctorHomMapLeft hE, Q.map_id, comp_id]

variable {E} in
/-- The derived hom `G = RHom_H(-, I)` is self-adjoint on the right, `G.rightOp ⊣ G`, with unit
the double-dual transformation, when the evaluation satisfies the triangle identity. -/
noncomputable def bifunctorRHomSelfAdjunction (hE : E.TriangleIdentity) :
    (bifunctorRHomOfComplex H I).rightOp ⊣ bifunctorRHomOfComplex H I where
  unit := bifunctorRHomBidual E hI
  counit :=
    { app X := ((bifunctorRHomBidual E hI).app X.unop).op
      naturality _ _ f :=
        Quiver.Hom.unop_inj ((bifunctorRHomBidual E hI).naturality f.unop).symm }
  left_triangle_components X := Quiver.Hom.unop_inj
    (congr_app (bifunctorRHomBidualTriangle_eq_id hI hE) (op X))
  right_triangle_components X := congr_app (bifunctorRHomBidualTriangle_eq_id hI hE) X

lemma bifunctorRHomSelfAdjunction_unit {E : BifunctorEvaluation H}
    (hE : E.TriangleIdentity) :
    (bifunctorRHomSelfAdjunction hI hE).unit = bifunctorRHomBidual E hI :=
  rfl


end DerivedCategory
