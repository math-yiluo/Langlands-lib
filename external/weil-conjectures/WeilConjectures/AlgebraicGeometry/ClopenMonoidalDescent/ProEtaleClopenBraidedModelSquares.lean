/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenBraidedUnitSquare

/-! # Cancellation of native braided model squares

Source: Stacks Project, Tags 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-model-squares).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  RingedDerivedNative.monoidal RingedDerivedNative.symmetric
  HasDerivedCategory.standard SheafOfModules.pushforward

attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  RingedDerivedNative.moduleClosed SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

namespace CategoryTheory

open Category Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_tensor_square_aux
    {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
    (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
    [Q.LaxMonoidal] [L.LaxMonoidal] [F.Monoidal] [G.Monoidal]
    (e : Q ⋙ G ≅ F ⋙ L) [NatTrans.IsMonoidal e.hom]
    (X Y : A) [IsIso (μ Q X Y)] [IsIso (μ L (F.obj X) (F.obj Y))] :
    G.map (inv (μ Q X Y)) ≫ δ G (Q.obj X) (Q.obj Y) ≫
        (e.hom.app X ⊗ₘ e.hom.app Y) =
      e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y) ≫ inv (μ L (F.obj X) (F.obj Y)) := by
  have hh := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
  simp only [comp_μ, Functor.comp_obj, Category.assoc] at hh
  apply (cancel_epi (G.map (μ Q X Y))).1
  simp only [← G.map_comp_assoc, IsIso.hom_inv_id, G.map_id, id_comp]
  apply (cancel_epi (μ G (Q.obj X) (Q.obj Y))).1
  simp only [Functor.Monoidal.μ_δ_assoc]
  apply (cancel_mono (μ L (F.obj X) (F.obj Y))).1
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [reassoc_of% hh]
  simp only [← L.map_comp, Functor.Monoidal.μ_δ, L.map_id, comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
/-- The native tensor and unit equations follow by cancellation from a monoidal
factorization. This is the algebraic square used by the normalization theorem.
Source: Stacks Project, Tags 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-model-squares).

Proof: instantiate the native lax structures and their K-flat isomorphism lemmas. Apply
monoidality of the factorization and cancel its tensor maps; the cochain tensorator is
replaced by the supplied summand-normalized comparison. Apply the unit equation similarly,
then unfold the canonical unit comparison. Every cancelled map is an isomorphism under the
stated K-flat hypotheses.
-/
theorem clopen_braided_model_squares
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y)
            ((clopenTensorRings.{t, u} j).obj R))
    (c : (clopenTensorComplexRestriction.{t, u} j R).Braided)
    (hcδ : ∀ P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      c.toMonoidal.toOplaxMonoidal.δ P Q = b.hom.app (P, Q))
    (hcη : c.toMonoidal.toOplaxMonoidal.η =
      ((HomologicalComplex.singleMapHomologicalComplex
        (clopenTensorRestriction.{t, u} j R) (.up ℤ) (0 : ℤ)).app
          (𝟙_ (clopenTensorModules.{t, u} R))).hom ≫
        (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map
          (clopenTensorUnitComparison.{t, u} j R h).hom)
    (d : (derivedRestriction.{t, u} j R).Braided) :
    letI := c
    letI := d
    letI := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology X) R
    letI := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) ((clopenTensorRings.{t, u} j).obj R)
    NatTrans.IsMonoidal (factors.{t, u} j R).hom →
      ModelNormalization.{t, u} j R b (braidedComparison.{t, u} j R d) ∧
        braidedUnit.{t, u} j R d = unitComparison.{t, u} j R h := by
  intro he
  let := c
  let := d
  let := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
    (topology X) R
  let := RingedDerivedNative.laxBraided.{t + 1, t, u, max (u + 1) (t + 2)}
    (topology Y) ((clopenTensorRings.{t, u} j).obj R)
  constructor
  · intro P Q hP hQ hflatP hflatQ hiP
    have hμX := RingedDerivedNative.isIso_mu.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology X) R P Q (Or.inl hP)
    have hμY := RingedDerivedNative.isIso_mu.{t + 1, t, u, max (u + 1) (t + 2)}
      (topology Y) ((clopenTensorRings.{t, u} j).obj R)
      ((clopenTensorComplexRestriction.{t, u} j R).obj P)
      ((clopenTensorComplexRestriction.{t, u} j R).obj Q) (Or.inl hiP)
    have hh := CategoryTheory.inverse_tensor_square_aux
      (Q := DerivedCategory.Q.{max (u + 1) (t + 2)})
      (L := DerivedCategory.Q.{max (u + 1) (t + 2)})
      (F := clopenTensorComplexRestriction.{t, u} j R)
      (G := derivedRestriction.{t, u} j R)
      (e := factors.{t, u} j R) P Q
    rw [hcδ P Q] at hh
    have heq : (factors.{t, u} j R).hom.app
        ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) =
        (factors.{t, u} j R).hom.app (P ⊗ Q) := by
      have hn := (factors.{t, u} j R).hom.naturality
        (eqToHom (RingedDerivedNative.totalTensor_eq (topology X) R P Q))
      simpa using hn.symm
    rw [heq]
    rw [RingedDerivedNative.tensorIso_hom (topology X) R P Q (Or.inl hP)]
    rw [RingedDerivedNative.tensorIso_hom (topology Y)
      ((clopenTensorRings.{t, u} j).obj R)
      ((clopenTensorComplexRestriction.{t, u} j R).obj P)
      ((clopenTensorComplexRestriction.{t, u} j R).obj Q) (Or.inl hiP)]
    simpa only [braidedComparison, Iso.symm_hom,
      Functor.Monoidal.μNatIso_inv_app] using hh
  · exact clopen_braided_unit_square.{t, u} j R h c hcη d he

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
