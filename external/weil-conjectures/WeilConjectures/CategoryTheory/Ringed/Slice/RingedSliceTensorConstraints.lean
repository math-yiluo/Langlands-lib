/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Associativity of normalized slice tensor comparison

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sfb-ringed-slice-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory
section TotalMapGeneric
universe a b
variable {A : Type a} [Category.{b} A] [Preadditive A]
  (G : A ⥤ A ⥤ A) [G.PreservesZeroMorphisms]
  [∀ X, (G.obj X).PreservesZeroMorphisms]
  [∀ P Q : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctor P Q G (.up ℤ)]
private theorem total_map_generic
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj (G.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).map
      (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom f g) =
      HomologicalComplex.mapBifunctorMap f g G (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap f (𝟙 Q) G (.up ℤ) ≫
    HomologicalComplex.mapBifunctorMap (𝟙 P') g G (.up ℤ) = _
  simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
end TotalMapGeneric
section Generic
universe a b x y
variable {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
  {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  {r : D ⥤ E} {K : Prop}
  (d : RingedSliceEvaluationComparisons H HU r S SU K)

private theorem nested_left_model
    {P Q N PQ L : D} {PU QU NU PQU LU : E}
    (i : PQ ≅ S.tensor.obj (P, Q)) (iL : L ≅ S.tensor.obj (PQ, N))
    (j : PQU ≅ SU.tensor.obj (PU, QU)) (jL : LU ≅ SU.tensor.obj (PQU, NU))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU) (aN : r.obj N ≅ NU)
    (c : r.obj PQ ≅ PQU) (cL : r.obj L ≅ LU)
    (h : r.map i.hom ≫ (d.rho P Q).hom ≫
      SU.tensor.map (aP.hom, aQ.hom) = c.hom ≫ j.hom)
    (hL : r.map iL.hom ≫ (d.rho PQ N).hom ≫
      SU.tensor.map (c.hom, aN.hom) = cL.hom ≫ jL.hom) :
    r.map (iL.hom ≫ S.tensor.map (i.hom, 𝟙 N)) ≫
      (d.rho (S.tensor.obj (P, Q)) N).hom ≫
      SU.tensor.map ((d.rho P Q).hom, 𝟙 (r.obj N)) ≫
      SU.tensor.map
        (X := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        (Y := (SU.tensor.obj (PU, QU), NU))
        (SU.tensor.map (aP.hom, aQ.hom), aN.hom) =
      cL.hom ≫ jL.hom ≫ SU.tensor.map (j.hom, 𝟙 NU) := by
  let := S.monoidal
  let := SU.monoidal
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (d.rho_naturality _ _ _ _ _ _)]
  simp only [Functor.map_id, ← Category.assoc, ← SU.tensor.map_comp]
  simp only [prod_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
  change r.map iL.hom ≫ (d.rho PQ N).hom ≫
    SU.tensor.map (X := (r.obj PQ, r.obj N))
      (Y := (SU.tensor.obj (PU, QU), NU))
      (r.map i.hom ≫ (d.rho P Q).hom ≫
        SU.tensor.map (aP.hom, aQ.hom), aN.hom) = _
  rw [h]
  have he : SU.tensor.map (X := (r.obj PQ, r.obj N))
      (Y := (SU.tensor.obj (PU, QU), NU)) (c.hom ≫ j.hom, aN.hom) =
      SU.tensor.map (X := (r.obj PQ, r.obj N)) (Y := (PQU, NU))
        (c.hom, aN.hom) ≫ SU.tensor.map
        (X := (PQU, NU)) (Y := (SU.tensor.obj (PU, QU), NU)) (j.hom, 𝟙 NU) := by
    rw [← SU.tensor.map_comp]
    simp only [prod_comp, Category.comp_id]
  rw [he]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ SU.tensor.map (X := (PQU, NU))
      (Y := (SU.tensor.obj (PU, QU), NU)) (j.hom, 𝟙 NU)) hL

private theorem nested_right_model
    {P Q N QN L : D} {PU QU NU QNU LU : E}
    (i : QN ≅ S.tensor.obj (Q, N)) (iL : L ≅ S.tensor.obj (P, QN))
    (j : QNU ≅ SU.tensor.obj (QU, NU)) (jL : LU ≅ SU.tensor.obj (PU, QNU))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU) (aN : r.obj N ≅ NU)
    (c : r.obj QN ≅ QNU) (cL : r.obj L ≅ LU)
    (h : r.map i.hom ≫ (d.rho Q N).hom ≫
      SU.tensor.map (aQ.hom, aN.hom) = c.hom ≫ j.hom)
    (hL : r.map iL.hom ≫ (d.rho P QN).hom ≫
      SU.tensor.map (aP.hom, c.hom) = cL.hom ≫ jL.hom) :
    r.map (iL.hom ≫ S.tensor.map (𝟙 P, i.hom)) ≫
      (d.rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (𝟙 (r.obj P), (d.rho Q N).hom) ≫
      SU.tensor.map
        (X := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (Y := (PU, SU.tensor.obj (QU, NU)))
        (aP.hom, SU.tensor.map (aQ.hom, aN.hom)) =
      cL.hom ≫ jL.hom ≫ SU.tensor.map (𝟙 PU, j.hom) := by
  let := S.monoidal
  let := SU.monoidal
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (d.rho_naturality _ _ _ _ _ _)]
  simp only [Functor.map_id, ← Category.assoc, ← SU.tensor.map_comp]
  simp only [prod_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
  change r.map iL.hom ≫ (d.rho P QN).hom ≫
    SU.tensor.map (X := (r.obj P, r.obj QN))
      (Y := (PU, SU.tensor.obj (QU, NU)))
      (aP.hom, r.map i.hom ≫ (d.rho Q N).hom ≫
        SU.tensor.map (aQ.hom, aN.hom)) = _
  rw [h]
  have he : SU.tensor.map (X := (r.obj P, r.obj QN))
      (Y := (PU, SU.tensor.obj (QU, NU))) (aP.hom, c.hom ≫ j.hom) =
      SU.tensor.map (X := (r.obj P, r.obj QN)) (Y := (PU, QNU))
        (aP.hom, c.hom) ≫ SU.tensor.map
        (X := (PU, QNU)) (Y := (PU, SU.tensor.obj (QU, NU))) (𝟙 PU, j.hom) := by
    rw [← SU.tensor.map_comp]
    simp only [prod_comp, Category.comp_id]
  rw [he]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ SU.tensor.map (X := (PU, QNU))
      (Y := (PU, SU.tensor.obj (QU, NU))) (𝟙 PU, j.hom)) hL
-- The associativity square has dependent comparison endpoints.
private theorem associator_of_models :
    ∀ {P Q N X Y : D} {PU QU NU XU YU : E}
    (i : X ≅ S.tensor.obj (S.tensor.obj (P, Q), N))
    (i' : Y ≅ S.tensor.obj (P, S.tensor.obj (Q, N)))
    (j : XU ≅ SU.tensor.obj (SU.tensor.obj (PU, QU), NU))
    (j' : YU ≅ SU.tensor.obj (PU, SU.tensor.obj (QU, NU)))
    (aP : r.obj P ≅ PU) (aQ : r.obj Q ≅ QU) (aN : r.obj N ≅ NU)
    (c : r.obj X ≅ XU) (c' : r.obj Y ≅ YU)
    (b : X ⟶ Y) (bU : XU ⟶ YU)
    (_hL : r.map i.hom ≫ (d.rho (S.tensor.obj (P, Q)) N).hom ≫
      SU.tensor.map (X := (r.obj (S.tensor.obj (P, Q)), r.obj N))
        (Y := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        ((d.rho P Q).hom, 𝟙 (r.obj N)) ≫
      SU.tensor.map (X := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        (Y := (SU.tensor.obj (PU, QU), NU))
        (SU.tensor.map (X := (r.obj P, r.obj Q)) (Y := (PU, QU))
          (aP.hom, aQ.hom), aN.hom) =
      c.hom ≫ j.hom)
    (_hR : r.map i'.hom ≫ (d.rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (X := (r.obj P, r.obj (S.tensor.obj (Q, N))))
        (Y := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (𝟙 (r.obj P), (d.rho Q N).hom) ≫
      SU.tensor.map (X := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (Y := (PU, SU.tensor.obj (QU, NU)))
        (aP.hom, SU.tensor.map (X := (r.obj Q, r.obj N)) (Y := (QU, NU))
          (aQ.hom, aN.hom)) =
      c'.hom ≫ j'.hom)
    (_hb : i.hom ≫ (S.monoidal.associator P Q N).hom = b ≫ i'.hom)
    (_hbU : j.hom ≫ (SU.monoidal.associator PU QU NU).hom = bU ≫ j'.hom)
    (_hc : r.map b ≫ c'.hom = c.hom ≫ bU),
    r.map (S.monoidal.associator P Q N).hom ≫
      (d.rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (X := (r.obj P, r.obj (S.tensor.obj (Q, N))))
        (Y := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (𝟙 (r.obj P), (d.rho Q N).hom) =
      (d.rho (S.tensor.obj (P, Q)) N).hom ≫
        SU.tensor.map (X := (r.obj (S.tensor.obj (P, Q)), r.obj N))
          (Y := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
          ((d.rho P Q).hom, 𝟙 (r.obj N)) ≫
        (SU.monoidal.associator (r.obj P) (r.obj Q) (r.obj N)).hom := by
  let := S.monoidal
  let := SU.monoidal
  intro P Q N X Y PU QU NU XU YU i i' j j' aP aQ aN c c' b bU hL hR hb hbU hc
  simp only [CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
    tensorHom_id, id_tensorHom] at hL hR ⊢
  have hi : IsIso (aP.hom ⊗ₘ (aQ.hom ⊗ₘ aN.hom)) := inferInstance
  apply (cancel_epi (r.map i.hom)).mp
  apply (cancel_mono (aP.hom ⊗ₘ (aQ.hom ⊗ₘ aN.hom))).mp
  calc
    _ = r.map b ≫ (r.map i'.hom ≫ (d.rho P (Q ⊗ N)).hom ≫
        r.obj P ◁ (d.rho Q N).hom ≫ (aP.hom ⊗ₘ (aQ.hom ⊗ₘ aN.hom))) := by
      simp only [← r.map_comp, ← Category.assoc, hb]
    _ = r.map b ≫ c'.hom ≫ j'.hom := by rw [hR]
    _ = c.hom ≫ bU ≫ j'.hom := by rw [← Category.assoc, hc, Category.assoc]
    _ = c.hom ≫ j.hom ≫ (α_ PU QU NU).hom := by
      rw [← hbU]
    _ = _ := by
      rw [← Category.assoc, ← hL]
      simp only [Category.assoc]
      rw [MonoidalCategory.associator_naturality]
private theorem associator_of_iso
    {P Q N L M V : D} (e : P ≅ L) (e' : Q ≅ M) (e'' : N ≅ V)
    (h : r.map (S.monoidal.associator P Q N).hom ≫
      (d.rho P (S.tensor.obj (Q, N))).hom ≫
      SU.tensor.map (X := (r.obj P, r.obj (S.tensor.obj (Q, N))))
        (Y := (r.obj P, SU.tensor.obj (r.obj Q, r.obj N)))
        (𝟙 (r.obj P), (d.rho Q N).hom) =
      (d.rho (S.tensor.obj (P, Q)) N).hom ≫
      SU.tensor.map (X := (r.obj (S.tensor.obj (P, Q)), r.obj N))
        (Y := (SU.tensor.obj (r.obj P, r.obj Q), r.obj N))
        ((d.rho P Q).hom, 𝟙 (r.obj N)) ≫
      (SU.monoidal.associator (r.obj P) (r.obj Q) (r.obj N)).hom) :
    r.map (S.monoidal.associator L M V).hom ≫
      (d.rho L (S.tensor.obj (M, V))).hom ≫
      SU.tensor.map (X := (r.obj L, r.obj (S.tensor.obj (M, V))))
        (Y := (r.obj L, SU.tensor.obj (r.obj M, r.obj V)))
        (𝟙 (r.obj L), (d.rho M V).hom) =
      (d.rho (S.tensor.obj (L, M)) V).hom ≫
      SU.tensor.map (X := (r.obj (S.tensor.obj (L, M)), r.obj V))
        (Y := (SU.tensor.obj (r.obj L, r.obj M), r.obj V))
        ((d.rho L M).hom, 𝟙 (r.obj V)) ≫
      (SU.monoidal.associator (r.obj L) (r.obj M) (r.obj V)).hom := by
  let := S.monoidal
  let := SU.monoidal
  let F₁ := (leftAssocTensor D) ⋙ r
  let F₂ := (rightAssocTensor D) ⋙ r
  let G₁ := (r.prod (r.prod r)) ⋙ leftAssocTensor E
  let G₂ := (r.prod (r.prod r)) ⋙ rightAssocTensor E
  let A : F₁ ⟶ F₂ := Functor.whiskerRight (associatorNatIso D).hom r
  let B : G₁ ⟶ G₂ := Functor.whiskerLeft (r.prod (r.prod r)) (associatorNatIso E).hom
  let c₁ : F₁ ⟶ G₁ :=
    { app := fun X ↦ (d.rho (X.1 ⊗ X.2.1) X.2.2).hom ≫
        (d.rho X.1 X.2.1).hom ▷ r.obj X.2.2
      naturality := by
        intro X Y f
        have h₁ := d.rho_naturality (X.1 ⊗ X.2.1) X.2.2
          (Y.1 ⊗ Y.2.1) Y.2.2 (f.1 ⊗ₘ f.2.1) f.2.2
        have h₂ := d.rho_naturality X.1 X.2.1 Y.1 Y.2.1 f.1 f.2.1
        simp only [CoefficientClosedStructure.tensor, tensor_map] at h₁ h₂
        change r.map ((f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2) ≫ _ = _
        rw [reassoc_of% h₁]
        change (d.rho (X.1 ⊗ X.2.1) X.2.2).hom ≫
            (r.map (f.1 ⊗ₘ f.2.1) ⊗ₘ r.map f.2.2) ≫
              (d.rho Y.1 Y.2.1).hom ▷ r.obj Y.2.2 = _
        simp only [← tensorHom_id, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₁, Functor.comp_map, Functor.prod_map,
          leftAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let c₂ : F₂ ⟶ G₂ :=
    { app := fun X ↦ (d.rho X.1 (X.2.1 ⊗ X.2.2)).hom ≫
        r.obj X.1 ◁ (d.rho X.2.1 X.2.2).hom
      naturality := by
        intro X Y f
        have h₁ := d.rho_naturality X.1 (X.2.1 ⊗ X.2.2)
          Y.1 (Y.2.1 ⊗ Y.2.2) f.1 (f.2.1 ⊗ₘ f.2.2)
        have h₂ := d.rho_naturality X.2.1 X.2.2 Y.2.1 Y.2.2 f.2.1 f.2.2
        simp only [CoefficientClosedStructure.tensor, tensor_map] at h₁ h₂
        change r.map (f.1 ⊗ₘ (f.2.1 ⊗ₘ f.2.2)) ≫ _ = _
        rw [reassoc_of% h₁]
        change (d.rho X.1 (X.2.1 ⊗ X.2.2)).hom ≫
            (r.map f.1 ⊗ₘ r.map (f.2.1 ⊗ₘ f.2.2)) ≫
              r.obj Y.1 ◁ (d.rho Y.2.1 Y.2.2).hom = _
        simp only [← id_tensorHom, Category.assoc,
          tensorHom_comp_tensorHom,
          Category.comp_id]
        erw [h₂]
        simp only [G₂, Functor.comp_map, Functor.prod_map,
          rightAssocTensor_map,
          tensorHom_comp_tensorHom,
          Category.id_comp] }
  let z : (P, Q, N) ≅ (L, M, V) := e.prod (e'.prod e'')
  have hz : IsIso (F₁.map z.hom) := inferInstance
  apply (cancel_epi (F₁.map z.hom)).mp
  have hh : (A ≫ c₂).app (P, Q, N) = (c₁ ≫ B).app (P, Q, N) := by
    simpa only [A, B, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      CoefficientClosedStructure.tensor, tensor_map,
      id_tensorHom, tensorHom_id, Category.assoc] using h
  have hh' := congrArg (fun f ↦ f ≫ G₂.map z.hom) hh
  rw [← (A ≫ c₂).naturality, ← (c₁ ≫ B).naturality] at hh'
  simpa only [A, B, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
      F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
      CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom, tensorHom_id, Category.assoc] using hh'
section RepresentativeComparison
universe a' b' x' y'
variable {V : Type a'} [Category.{x'} V] {W : Type b'} [Category.{y'} W]

/-- Transfer a complex-level associativity square through two localization functors.
The quotient functors and the two tensor functors remain abstract throughout this
calculation; only the displayed representative comparison equations are used. -/
private theorem associator_of_representative_comparisons
    (q : V ⥤ D) (qU : W ⥤ E) (F : V ⥤ W)
    (A : V × V ⥤ V) (AU : W × W ⥤ W) (α : q ⋙ r ≅ F ⋙ qU)
    (P Q N : V)
    (γPQ : F.obj (A.obj (P, Q)) ≅ AU.obj (F.obj P, F.obj Q))
    (γQN : F.obj (A.obj (Q, N)) ≅ AU.obj (F.obj Q, F.obj N))
    (γL : F.obj (A.obj (A.obj (P, Q), N)) ≅
      AU.obj (F.obj (A.obj (P, Q)), F.obj N))
    (γR : F.obj (A.obj (P, A.obj (Q, N))) ≅
      AU.obj (F.obj P, F.obj (A.obj (Q, N))))
    (a : A.obj (A.obj (P, Q), N) ≅ A.obj (P, A.obj (Q, N)))
    (aU : AU.obj (AU.obj (F.obj P, F.obj Q), F.obj N) ≅
      AU.obj (F.obj P, AU.obj (F.obj Q, F.obj N)))
    (tPQ : q.obj (A.obj (P, Q)) ≅ S.tensor.obj (q.obj P, q.obj Q))
    (tQN : q.obj (A.obj (Q, N)) ≅ S.tensor.obj (q.obj Q, q.obj N))
    (tL : q.obj (A.obj (A.obj (P, Q), N)) ≅
      S.tensor.obj (q.obj (A.obj (P, Q)), q.obj N))
    (tR : q.obj (A.obj (P, A.obj (Q, N))) ≅
      S.tensor.obj (q.obj P, q.obj (A.obj (Q, N))))
    (uPQ : qU.obj (AU.obj (F.obj P, F.obj Q)) ≅
      SU.tensor.obj (qU.obj (F.obj P), qU.obj (F.obj Q)))
    (uQN : qU.obj (AU.obj (F.obj Q, F.obj N)) ≅
      SU.tensor.obj (qU.obj (F.obj Q), qU.obj (F.obj N)))
    (uL : qU.obj (AU.obj (AU.obj (F.obj P, F.obj Q), F.obj N)) ≅
      SU.tensor.obj (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
    (uR : qU.obj (AU.obj (F.obj P, AU.obj (F.obj Q, F.obj N))) ≅
      SU.tensor.obj (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
    (uL₀ : qU.obj (AU.obj (F.obj (A.obj (P, Q)), F.obj N)) ≅
      SU.tensor.obj (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
    (uR₀ : qU.obj (AU.obj (F.obj P, F.obj (A.obj (Q, N)))) ≅
      SU.tensor.obj (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
    (hePQ : r.map tPQ.hom ≫ (d.rho (q.obj P) (q.obj Q)).hom ≫
      SU.tensor.map (X := (r.obj (q.obj P), r.obj (q.obj Q)))
        (Y := (qU.obj (F.obj P), qU.obj (F.obj Q))) (α.hom.app P, α.hom.app Q) =
      α.hom.app (A.obj (P, Q)) ≫ qU.map γPQ.hom ≫ uPQ.hom)
    (heQN : r.map tQN.hom ≫ (d.rho (q.obj Q) (q.obj N)).hom ≫
      SU.tensor.map (X := (r.obj (q.obj Q), r.obj (q.obj N)))
        (Y := (qU.obj (F.obj Q), qU.obj (F.obj N))) (α.hom.app Q, α.hom.app N) =
      α.hom.app (A.obj (Q, N)) ≫ qU.map γQN.hom ≫ uQN.hom)
    (heL : r.map tL.hom ≫ (d.rho (q.obj (A.obj (P, Q))) (q.obj N)).hom ≫
      SU.tensor.map (X := (r.obj (q.obj (A.obj (P, Q))), r.obj (q.obj N)))
        (Y := (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
        (α.hom.app (A.obj (P, Q)), α.hom.app N) =
      α.hom.app (A.obj (A.obj (P, Q), N)) ≫ qU.map γL.hom ≫ uL₀.hom)
    (heR : r.map tR.hom ≫ (d.rho (q.obj P) (q.obj (A.obj (Q, N)))).hom ≫
      SU.tensor.map (X := (r.obj (q.obj P), r.obj (q.obj (A.obj (Q, N)))))
        (Y := (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
        (α.hom.app P, α.hom.app (A.obj (Q, N))) =
      α.hom.app (A.obj (P, A.obj (Q, N))) ≫ qU.map γR.hom ≫ uR₀.hom)
    (hea : tL.hom ≫ S.tensor.map (X := (q.obj (A.obj (P, Q)), q.obj N))
        (Y := (S.tensor.obj (q.obj P, q.obj Q), q.obj N)) (tPQ.hom, 𝟙 _) ≫
      (S.monoidal.associator (q.obj P) (q.obj Q) (q.obj N)).hom =
      q.map a.hom ≫ tR.hom ≫ S.tensor.map
        (X := (q.obj P, q.obj (A.obj (Q, N))))
        (Y := (q.obj P, S.tensor.obj (q.obj Q, q.obj N))) (𝟙 _, tQN.hom))
    (heaU : uL.hom ≫ SU.tensor.map
        (X := (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
        (Y := (SU.tensor.obj (qU.obj (F.obj P), qU.obj (F.obj Q)), qU.obj (F.obj N)))
        (uPQ.hom, 𝟙 _) ≫
      (SU.monoidal.associator (qU.obj (F.obj P)) (qU.obj (F.obj Q)) (qU.obj (F.obj N))).hom =
      qU.map aU.hom ≫ uR.hom ≫ SU.tensor.map
        (X := (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
        (Y := (qU.obj (F.obj P), SU.tensor.obj (qU.obj (F.obj Q), qU.obj (F.obj N))))
        (𝟙 _, uQN.hom))
    (hnL : qU.map (AU.map (X := (F.obj (A.obj (P, Q)), F.obj N))
        (Y := (AU.obj (F.obj P, F.obj Q), F.obj N)) (γPQ.hom, 𝟙 _)) ≫ uL.hom =
      uL₀.hom ≫ SU.tensor.map
        (X := (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
        (Y := (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
        (qU.map γPQ.hom, 𝟙 _))
    (hnR : qU.map (AU.map (X := (F.obj P, F.obj (A.obj (Q, N))))
        (Y := (F.obj P, AU.obj (F.obj Q, F.obj N))) (𝟙 _, γQN.hom)) ≫ uR.hom =
      uR₀.hom ≫ SU.tensor.map
        (X := (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
        (Y := (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
        (𝟙 _, qU.map γQN.hom))
    (hc : F.map a.hom ≫ γR.hom ≫ AU.map
        (X := (F.obj P, F.obj (A.obj (Q, N))))
        (Y := (F.obj P, AU.obj (F.obj Q, F.obj N))) (𝟙 _, γQN.hom) =
      γL.hom ≫ AU.map (X := (F.obj (A.obj (P, Q)), F.obj N))
        (Y := (AU.obj (F.obj P, F.obj Q), F.obj N)) (γPQ.hom, 𝟙 _) ≫ aU.hom) :
    r.map (S.monoidal.associator (q.obj P) (q.obj Q) (q.obj N)).hom ≫
      (d.rho (q.obj P) (S.tensor.obj (q.obj Q, q.obj N))).hom ≫
      SU.tensor.map (X := (r.obj (q.obj P), r.obj (S.tensor.obj (q.obj Q, q.obj N))))
        (Y := (r.obj (q.obj P), SU.tensor.obj (r.obj (q.obj Q), r.obj (q.obj N))))
        (𝟙 _, (d.rho (q.obj Q) (q.obj N)).hom) =
      (d.rho (S.tensor.obj (q.obj P, q.obj Q)) (q.obj N)).hom ≫
      SU.tensor.map (X := (r.obj (S.tensor.obj (q.obj P, q.obj Q)), r.obj (q.obj N)))
        (Y := (SU.tensor.obj (r.obj (q.obj P), r.obj (q.obj Q)), r.obj (q.obj N)))
        ((d.rho (q.obj P) (q.obj Q)).hom, 𝟙 _) ≫
      (SU.monoidal.associator (r.obj (q.obj P)) (r.obj (q.obj Q)) (r.obj (q.obj N))).hom := by
  let i := tL ≪≫ S.tensor.mapIso (tPQ.prod (Iso.refl _))
  let i' := tR ≪≫ S.tensor.mapIso ((Iso.refl _).prod tQN)
  let j := uL ≪≫ SU.tensor.mapIso (uPQ.prod (Iso.refl _))
  let j' := uR ≪≫ SU.tensor.mapIso ((Iso.refl _).prod uQN)
  let c := α.app (A.obj (A.obj (P, Q), N)) ≪≫ qU.mapIso γL ≪≫
    qU.mapIso (AU.mapIso (γPQ.prod (Iso.refl (F.obj N))))
  let c' := α.app (A.obj (P, A.obj (Q, N))) ≪≫ qU.mapIso γR ≪≫
    qU.mapIso (AU.mapIso ((Iso.refl (F.obj P)).prod γQN))
  have hL := nested_left_model S SU d tPQ tL uPQ uL
    (α.app P) (α.app Q) (α.app N)
    (α.app (A.obj (P, Q)) ≪≫ qU.mapIso γPQ) c
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using hePQ) (by
      dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Category.assoc, Iso.prod_hom, Iso.refl_hom, Prod.mkHom]
      rw [hnL]
      have hh := congrArg (fun f ↦ f ≫ SU.tensor.map
        (X := (qU.obj (F.obj (A.obj (P, Q))), qU.obj (F.obj N)))
        (Y := (qU.obj (AU.obj (F.obj P, F.obj Q)), qU.obj (F.obj N)))
        (qU.map γPQ.hom, 𝟙 _)) heL
      simpa only [Category.assoc, ← SU.tensor.map_comp, prod_comp,
        Category.id_comp, Category.comp_id, Iso.app_hom, Iso.trans_hom,
        Functor.mapIso_hom, Prod.mkHom] using hh)
  have hR := nested_right_model S SU d tQN tR uQN uR
    (α.app P) (α.app Q) (α.app N)
    (α.app (A.obj (Q, N)) ≪≫ qU.mapIso γQN) c'
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using heQN) (by
      dsimp only [c', Iso.trans_hom, Functor.mapIso_hom]
      simp only [Category.assoc, Iso.prod_hom, Iso.refl_hom, Prod.mkHom]
      rw [hnR]
      have hh := congrArg (fun f ↦ f ≫ SU.tensor.map
        (X := (qU.obj (F.obj P), qU.obj (F.obj (A.obj (Q, N)))))
        (Y := (qU.obj (F.obj P), qU.obj (AU.obj (F.obj Q, F.obj N))))
        (𝟙 _, qU.map γQN.hom)) heR
      simpa only [Category.assoc, ← SU.tensor.map_comp, prod_comp,
        Category.id_comp, Category.comp_id, Iso.app_hom, Iso.trans_hom,
        Functor.mapIso_hom, Prod.mkHom] using hh)
  apply associator_of_models S SU d i i' j j'
    (α.app P) (α.app Q) (α.app N) c c' (q.map a.hom) (qU.map aU.hom)
    (by
      dsimp only [i, j, Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      simpa only [Prod.mkHom, Category.assoc] using hL)
    (by
      dsimp only [i', j', Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      simpa only [Prod.mkHom, Category.assoc] using hR)
    (by
      dsimp only [i, i', Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      exact (Category.assoc _ _ _).trans hea)
    (by
      dsimp only [j, j', Iso.trans_hom, Functor.mapIso_hom, Iso.prod,
        Iso.refl, Prod.mkHom]
      exact (Category.assoc _ _ _).trans heaU)
  dsimp only [c, c', Iso.trans_hom, Functor.mapIso_hom, Iso.prod, Iso.refl, Prod.mkHom]
  simp only [Category.assoc, Iso.app_hom]
  rewrite [reassoc_of% α.hom.naturality a.hom]
  have hh := congrArg (fun f ↦ α.hom.app _ ≫ qU.map f) hc
  simpa only [Functor.map_comp, Category.assoc] using hh

end RepresentativeComparison

end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (T : CoefficientTensorModels.{r, c, v, w} J R S)
  (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ S.monoidal)
  (K : RingedDerivedTensorCoherence.{c, v, r, w} J R S T s)
  (SU : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)))
  (TU : CoefficientTensorModels.{r, max c v, v, w'} (J.over U) (R.over U) SU)
  (sU : @SymmetricCategory
    (DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    _ SU.monoidal)
  (KU : RingedDerivedTensorCoherence.{max c v, v, r, w'} (J.over U) (R.over U) SU TU sU)
  (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, r, w} J R)
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
    (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) S SU
    (RingedSliceFlatRestriction.{c, v, r} J R U))
  (hd : RingedSliceEvaluationNormalized.{c, v, r, w, w'} J R U S T SU TU d)

-- Keep the representative predicate parametric in the localized functor.
/-- The tensor normalization formula with its restriction functor and localization
comparison as parameters, so coherence checks do not unfold their constructions. -/
private def SliceTensorModelFor
    (r₀ : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
      DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    (α : DerivedCategory.Q ⋙ r₀ ≅
      ringedSliceComplexRestriction.{c, v, r} J R U ⋙ DerivedCategory.Q)
    (d₀ : RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{c, v, r, w} J R)
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      r₀ S SU (RingedSliceFlatRestriction.{c, v, r} J R U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v
    r} RingCat.{max c v r})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (fP : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (P.X
      n))
    (fQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (Q.X
      n)),
    ∃ γ : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P,
          (ringedSliceComplexRestriction.{c, v, r} J R U).obj Q),
      (∀ (p q k : ℤ) (h : p + q = k) (V : Over U)
        (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
        (γ.hom.f k).val.app (op V)
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h (op V.left) x y) =
        coefficientTensorGenerator.{r, max c v, v} (J.over U) (R.over U)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj Q) p q k h (op V) x y) ∧
      (r₀).map
          (T.iso J R S P Q hP hQ).hom ≫
        (d₀.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        SU.tensor.map
          (X := ((r₀).obj (DerivedCategory.Q.obj
            P), (r₀).obj (DerivedCategory.Q.obj
            Q)))
          (Y := (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, r} J R U).obj Q)))
          ((α).hom.app P,
            (α).hom.app Q) =
      (α).hom.app
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map γ.hom ≫
        (TU.iso (J.over U) (R.over U) SU
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P)
          ((ringedSliceComplexRestriction.{c, v, r} J R U).obj Q)
          (d₀.kflat P hP fP).1 (d₀.kflat Q hQ fQ).1).hom

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem tensorGenerator_map
    {P P' Q Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℤ) (hpq : p + q = k)
    (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{r, c, v} J R).map
      (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom f g)).f k).val.app U
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y) =
    coefficientTensorGenerator.{r, c, v} J R P' Q' p q k hpq U
      ((f.f p).val.app U x) ((g.f q).val.app U y) := by
  subst k
  let := SheafOfModules.monoidalCategory R
  unfold coefficientTotalTensor
  rewrite [total_map_generic]
  have h := HomologicalComplex.ι_mapBifunctorMap f g
    (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) p q (p + q) rfl
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at h
  rw [← Category.assoc, ← tensorHom_def] at h
  have hh := congrArg (fun a ↦ a.val.app U
    (CochainPullback.moduleTmul (P.X p) (Q.X q) U x y)) h
  have hm := CochainPullback.moduleTmul_map (f.f p) (g.f q) U x y
  exact hh.trans (congrArg
    ((HomologicalComplex.ιMapBifunctor P' Q'
      (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) p q (p + q) rfl).val.app U) hm)
omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
private theorem tensor_flat
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (fP : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (P.X n))
    (fQ : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (Q.X n)) :
    ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R)
      (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n) := by
  exact SheafOfModules.KFlatTotalTensorModel.totalFlat R P Q fP fQ

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- Restriction identifies the two section modules by the identity function. -/
private def sliceSection
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) (k : ℤ) (V : (Over U)ᵒᵖ) :
    (P.X k).val.obj (op V.unop.left) ≃
      (((ringedSliceComplexRestriction.{c, v, r} J R U).obj P).X k).val.obj V :=
  Equiv.refl _

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- The section identification is natural in maps of complexes. -/
private theorem slice_map_section
    {P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ} (f : P ⟶ Q)
    (k : ℤ) (V : (Over U)ᵒᵖ) (x : (P.X k).val.obj (op V.unop.left)) :
    ((((ringedSliceComplexRestriction.{c, v, r} J R U).map f).f k).val.app V)
      (sliceSection.{c, v, r} J R U P k V x) =
    sliceSection.{c, v, r} J R U Q k V ((f.f k).val.app (op V.unop.left) x) := by
  rfl

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- A total tensor functor with its section generators and their detecting property. -/
private structure TensorPresentation where
  tensor : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ×
    CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
      CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ
  generator : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (p q k : ℤ) (_h : p + q = k) (V : Cᵒᵖ),
    (P.X p).val.obj V → (Q.X q).val.obj V → ((tensor.obj (P, Q)).X k).val.obj V
  map_generator : ∀ {P P' Q Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℤ) (hpq : p + q = k)
    (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    (((tensor.map (Prod.mkHom f g)).f k).val.app V)
      (generator P Q p q k hpq V x y) =
    generator P' Q' p q k hpq V ((f.f p).val.app V x) ((g.f q).val.app V y)
  ext_three : ∀ (P Q N F : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (φ ψ : tensor.obj (tensor.obj (P, Q), N) ⟶ F),
    (∀ (p q n pq k : ℤ) (hpq : p + q = pq) (hpn : pq + n = k) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X n).val.obj V),
      (φ.f k).val.app V (generator (tensor.obj (P, Q)) N pq n k hpn V
        (generator P Q p q pq hpq V x y) z) =
      (ψ.f k).val.app V (generator (tensor.obj (P, Q)) N pq n k hpn V
        (generator P Q p q pq hpq V x y) z)) → φ = ψ

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- The actual total tensor, packaged with its proved generator interface. -/
private def tensorPresentation : TensorPresentation.{c, v, r} J R where
  tensor := coefficientTotalTensor.{r, c, v} J R
  generator := coefficientTensorGenerator.{r, c, v} J R
  map_generator := tensorGenerator_map.{c, v, r} J R
  ext_three := tensorGenerator_ext₃.{c, v, r} J R

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  derivedInternalHomOfUniverses ringedSliceDerivedRestriction ringedSliceLocalizationIso

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- The pure-generator property of a termwise tensor restriction comparison. -/
private def SliceTensorRawGeneratorFormula
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (γ : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P,
          (ringedSliceComplexRestriction.{c, v, r} J R U).obj Q)) : Prop :=
  ∀ (p q k : ℤ) (hpq : p + q = k) (V : Over U)
    (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
    (γ.hom.f k).val.app (op V)
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq (op V.left) x y) =
    coefficientTensorGenerator.{r, max c v, v} (J.over U) (R.over U)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P)
      ((ringedSliceComplexRestriction.{c, v, r} J R U).obj Q) p q k hpq (op V) x y

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- The pure-generator property of a termwise tensor restriction comparison. -/
private def SliceTensorGeneratorFormulaFor
    (X : TensorPresentation.{c, v, r} J R)
    (Y : TensorPresentation.{max c v, v, r} (J.over U) (R.over U))
    (F₀ : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
      CochainComplex (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)) ℤ)
    (e : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (k : ℤ) (V : (Over U)ᵒᵖ), (P.X k).val.obj (op V.unop.left) ≃
        ((F₀.obj P).X k).val.obj V)
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (γ : F₀.obj
      (X.tensor.obj (P, Q)) ≅
      Y.tensor.obj
        (F₀.obj P,
          F₀.obj Q)) : Prop :=
  ∀ (p q k : ℤ) (hpq : p + q = k) (V : Over U)
    (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
    (γ.hom.f k).val.app (op V)
      (e (X.tensor.obj (P, Q)) k (op V)
        (X.generator P Q p q k hpq (op V.left) x y)) =
    Y.generator
      (F₀.obj P)
      (F₀.obj Q) p q k hpq (op V)
      (e P p (op V) x) (e Q q (op V) y)

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- The original normalization formula gives the formula with explicit section maps. -/
private theorem sliceGeneratorFormula_of_raw
    (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (γ : (ringedSliceComplexRestriction.{c, v, r} J R U).obj
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, r} J R U).obj P,
          (ringedSliceComplexRestriction.{c, v, r} J R U).obj Q))
    (h : SliceTensorRawGeneratorFormula.{c, v, r} J R U P Q γ) :
    SliceTensorGeneratorFormulaFor.{c, v, r} J R U
      (tensorPresentation.{c, v, r} J R)
      (tensorPresentation.{max c v, v, r} (J.over U) (R.over U))
      (ringedSliceComplexRestriction.{c, v, r} J R U)
      (sliceSection.{c, v, r} J R U) P Q γ := by
  exact h

private def SliceTensorModelComplex
    (F₀ : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
      CochainComplex (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)) ℤ)
    (e : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (k : ℤ) (V : (Over U)ᵒᵖ), (P.X k).val.obj (op V.unop.left) ≃
        ((F₀.obj P).X k).val.obj V)
    (Fflat : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (_fP : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (P.X n)),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := J.over U) (R := R.over U) (F₀.obj P))
    (r₀ : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
      DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    (α : DerivedCategory.Q ⋙ r₀ ≅
      F₀ ⋙ DerivedCategory.Q)
    (d₀ : RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{c, v, r, w} J R)
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      r₀ S SU (RingedSliceFlatRestriction.{c, v, r} J R U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v
    r} RingCat.{max c v r})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (fP : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (P.X
      n))
    (fQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (J := J) (R := R) (Q.X
      n)),
    ∃ γ : (F₀).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)).obj
        ((F₀).obj P,
          (F₀).obj Q),
      SliceTensorGeneratorFormulaFor.{c, v, r} J R U
      (tensorPresentation.{c, v, r} J R)
      (tensorPresentation.{max c v, v, r} (J.over U) (R.over U)) F₀ e P Q γ ∧
      (r₀).map
          (T.iso J R S P Q hP hQ).hom ≫
        (d₀.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        SU.tensor.map
          (X := ((r₀).obj (DerivedCategory.Q.obj
            P), (r₀).obj (DerivedCategory.Q.obj
            Q)))
          (Y := (DerivedCategory.Q.obj ((F₀).obj P),
            DerivedCategory.Q.obj ((F₀).obj Q)))
          ((α).hom.app P,
            (α).hom.app Q) =
      (α).hom.app
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map γ.hom ≫
        (TU.iso (J.over U) (R.over U) SU
          ((F₀).obj P)
          ((F₀).obj Q)
          (Fflat P hP fP) (Fflat Q hQ fQ)).hom

-- Check the normalization predicate through its section and flatness interfaces.
/-- Package native restriction using its section and flatness interfaces. -/
private theorem sliceTensorModel_complex
    (r₀ : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
      DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    (α : DerivedCategory.Q ⋙ r₀ ≅
      ringedSliceComplexRestriction.{c, v, r} J R U ⋙ DerivedCategory.Q)
    (d₀ : RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{c, v, r, w} J R)
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      r₀ S SU (RingedSliceFlatRestriction.{c, v, r} J R U))
    (hmodel : SliceTensorModelFor J R U S T SU TU r₀ α d₀) :
    SliceTensorModelComplex J R U S T SU TU
      (ringedSliceComplexRestriction.{c, v, r} J R U)
      (sliceSection.{c, v, r} J R U)
      (fun P hP fP ↦ (d₀.kflat P hP fP).1) r₀ α d₀ := by
  intro P Q hP hQ fP fQ
  rcases hmodel P Q hP hQ fP fQ with ⟨γ, hγ, hEq⟩
  exact ⟨γ, sliceGeneratorFormula_of_raw.{c, v, r} J R U P Q γ hγ, hEq⟩

attribute [local irreducible] sliceSection

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))] in
/-- The generator property of the ordinary total-complex reassociation map. -/
private def TensorAssociatorFormula
    (X : TensorPresentation.{c, v, r} J R)
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (a : X.tensor.obj
      (X.tensor.obj (P, Q), N) ≅
      X.tensor.obj
        (P, X.tensor.obj (Q, N))) : Prop :=
  ∀ (p q n pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + n = qr)
    (hpk : pq + n = k) (hkr : p + qr = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X n).val.obj V),
    (a.hom.f k).val.app V
      (X.generator
        (X.tensor.obj (P, Q)) N pq n k hpk V
        (X.generator P Q p q pq hpq V x y) z) =
    X.generator P
      (X.tensor.obj (Q, N)) p qr k hkr V x
      (X.generator Q N q n qr hqr V y z)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Keep the section and total-tensor endpoints fixed during the comparison calculation.
omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
/-- Termwise restriction respects reassociation on normalized tensor comparisons.
Source: Stacks 07A4 and 0FPT. Cancel the left comparison, test on three pure
sections, and apply the four generator formulas and the two reassociation formulas.
Keeping these complex isomorphisms as parameters avoids unfolding their derived
representative constructions during the section calculation. -/
private theorem slice_tensor_associator_square
    (X : TensorPresentation.{c, v, r} J R)
    (Y : TensorPresentation.{max c v, v, r} (J.over U) (R.over U))
    (F₀ : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
      CochainComplex (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)) ℤ)
    (e : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (k : ℤ) (V : (Over U)ᵒᵖ), (P.X k).val.obj (op V.unop.left) ≃
        ((F₀.obj P).X k).val.obj V)
    (he : ∀ {P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
      (f : P ⟶ Q) (k : ℤ) (V : (Over U)ᵒᵖ) (x : (P.X k).val.obj (op V.unop.left)),
      (((F₀.map f).f k).val.app V) (e P k V x) =
        e Q k V ((f.f k).val.app (op V.unop.left) x))
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (a : X.tensor.obj
      (X.tensor.obj (P, Q), N) ≅
      X.tensor.obj
        (P, X.tensor.obj (Q, N)))
    (aU : Y.tensor.obj
      (Y.tensor.obj
        (F₀.obj P,
          F₀.obj Q),
        F₀.obj N) ≅
      Y.tensor.obj
        (F₀.obj P,
          Y.tensor.obj
            (F₀.obj Q,
              F₀.obj N)))
    (γPQ : F₀.obj
      (X.tensor.obj (P, Q)) ≅
      Y.tensor.obj
        (F₀.obj P,
          F₀.obj Q))
    (γQN : F₀.obj
      (X.tensor.obj (Q, N)) ≅
      Y.tensor.obj
        (F₀.obj Q,
          F₀.obj N))
    (γL : F₀.obj
      (X.tensor.obj
        (X.tensor.obj (P, Q), N)) ≅
      Y.tensor.obj
        (F₀.obj
          (X.tensor.obj (P, Q)),
          F₀.obj N))
    (γR : F₀.obj
      (X.tensor.obj
        (P, X.tensor.obj (Q, N))) ≅
      Y.tensor.obj
        (F₀.obj P,
          F₀.obj
            (X.tensor.obj (Q, N))))
    (hγPQ : SliceTensorGeneratorFormulaFor.{c, v, r} J R U X Y F₀ e P Q γPQ)
    (hγQN : SliceTensorGeneratorFormulaFor.{c, v, r} J R U X Y F₀ e Q N γQN)
    (hγL : SliceTensorGeneratorFormulaFor.{c, v, r} J R U X Y F₀ e
      (X.tensor.obj (P, Q)) N γL)
    (hγR : SliceTensorGeneratorFormulaFor.{c, v, r} J R U X Y F₀ e P
      (X.tensor.obj (Q, N)) γR)
    (ha : TensorAssociatorFormula.{c, v, r} J R X P Q N a)
    (haU : TensorAssociatorFormula.{max c v, v, r} (J.over U) (R.over U) Y
      (F₀.obj P)
      (F₀.obj Q)
      (F₀.obj N) aU) :
    F₀.map a.hom ≫ γR.hom ≫
      Y.tensor.map
        (X := (F₀.obj P,
          F₀.obj
            (X.tensor.obj (Q, N))))
        (Y := (F₀.obj P,
          Y.tensor.obj
            (F₀.obj Q,
              F₀.obj N)))
        (𝟙 _, γQN.hom) =
    γL.hom ≫ Y.tensor.map
      (X := (F₀.obj
        (X.tensor.obj (P, Q)),
          F₀.obj N))
      (Y := (Y.tensor.obj
        (F₀.obj P,
          F₀.obj Q),
        F₀.obj N))
      (γPQ.hom, 𝟙 _) ≫ aU.hom := by
  unfold SliceTensorGeneratorFormulaFor at hγPQ hγQN hγL hγR
  unfold TensorAssociatorFormula at ha haU
  let F := F₀
  let A := X.tensor
  let AU := Y.tensor
  let cL := γL ≪≫ AU.mapIso (γPQ.prod (Iso.refl (F.obj N)))
  have hcm : γL.hom ≫ AU.map (X := (F.obj (A.obj (P, Q)), F.obj N))
      (Y := (AU.obj (F.obj P, F.obj Q), F.obj N))
      (γPQ.hom, 𝟙 (F.obj N)) = cL.hom := rfl
  -- Keep the total tensor opaque until the generator formulas agree.
  conv_rhs => rw [← Category.assoc, hcm]
  apply (cancel_epi cL.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply Y.ext_three
  intro p q n pq k hpq hpk V
  refine (e P p V).surjective.forall.mpr fun x ↦ ?_
  refine (e Q q V).surjective.forall.mpr fun y ↦ ?_
  refine (e N n V).surjective.forall.mpr fun z ↦ ?_
  let qr := q + n
  have hqr : q + n = qr := rfl
  have hkr : p + qr = k := by omega
  have hcl : (cL.hom.f k).val.app V
      (e (A.obj (A.obj (P, Q), N)) k V
        (X.generator (A.obj (P, Q)) N pq n k hpk
          (op V.unop.left)
          (X.generator P Q p q pq hpq
            (op V.unop.left) x y) z)) =
      Y.generator
        (AU.obj (F.obj P, F.obj Q)) (F.obj N) pq n k hpk V
        (Y.generator
          (F.obj P) (F.obj Q) p q pq hpq V
          (e P p V x) (e Q q V y))
        (e N n V z) := by
    simp only [cL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    rewrite [hγL, Y.map_generator]
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app]
    exact congrArg (fun t ↦
      Y.generator
        (AU.obj (F.obj P, F.obj Q)) (F.obj N) pq n k hpk V t
        (e N n V z)) (hγPQ p q pq hpq V.unop x y)
  have hci := congrArg ((cL.inv.f k).val.app V) hcl
  have hi := congrArg (fun f ↦ (f.f k).val.app V
      (e (A.obj (A.obj (P, Q), N)) k V
        (X.generator (A.obj (P, Q)) N pq n k hpk
          (op V.unop.left)
          (X.generator P Q p q pq hpq
            (op V.unop.left) x y) z))) cL.hom_inv_id
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.hom_id, LinearMap.id_apply] at hi
  have hinv := hci.symm.trans hi
  let m := ((AU.map (X := (F.obj P, F.obj (A.obj (Q, N))))
      (Y := (F.obj P, AU.obj (F.obj Q, F.obj N)))
      (𝟙 (F.obj P), γQN.hom)).f k).val.app V
  let g := (γR.hom.f k).val.app V
  let b := ((F.map a.hom).f k).val.app V
  change m (g (b ((cL.inv.f k).val.app V _))) = _
  refine (congrArg (fun t ↦ m (g (b t))) hinv).trans ?_
  refine (congrArg (fun t ↦ m (g t))
    (he a.hom k V _)).trans ?_
  refine (congrArg (fun t ↦ m (g
    (e (A.obj (P, A.obj (Q, N))) k V t)))
    (ha p q n pq qr k hpq hqr hpk hkr (op V.unop.left) x y z)).trans ?_
  refine (congrArg m (hγR p qr k hkr V.unop x
    (X.generator Q N q n qr hqr
      (op V.unop.left) y z))).trans ?_
  refine (Y.map_generator
    (P := F.obj P) (P' := F.obj P)
    (Q := F.obj (A.obj (Q, N))) (Q' := AU.obj (F.obj Q, F.obj N))
    (𝟙 (F.obj P)) γQN.hom p qr k hkr V (e P p V x)
    (e (A.obj (Q, N)) qr V
      (X.generator Q N q n qr hqr
        (op V.unop.left) y z))).trans ?_
  change Y.generator
    (F.obj P) (AU.obj (F.obj Q, F.obj N)) p qr k hkr V
    (e P p V x)
    ((γQN.hom.f qr).val.app V
      (e (A.obj (Q, N)) qr V
        (X.generator Q N q n qr hqr
          (op V.unop.left) y z))) = _
  refine (congrArg (fun t ↦
    Y.generator
      (F.obj P) (AU.obj (F.obj Q, F.obj N)) p qr k hkr V
      (e P p V x) t)
    (hγQN q n qr hqr V.unop y z)).trans ?_
  exact (haU p q n pq qr k hpq hqr hpk hkr V
    (e P p V x) (e Q q V y)
    (e N n V z)).symm

attribute [local irreducible] DerivedCategory.Q ringedSliceComplexRestriction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Use the normalization API without unfolding the constructed derived functor.
include K KU in
/-- Associativity follows from the representative tensor-square predicate for any
localized functor and comparison. These parameters remain abstract during checking. -/
private theorem sliceTensorModel_associator
    (F₀ : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
      CochainComplex (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)) ℤ)
    (e : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (k : ℤ) (V : (Over U)ᵒᵖ), (P.X k).val.obj (op V.unop.left) ≃
        ((F₀.obj P).X k).val.obj V)
    (he : ∀ {P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
      (f : P ⟶ Q) (k : ℤ) (V : (Over U)ᵒᵖ) (x : (P.X k).val.obj (op V.unop.left)),
      (((F₀.map f).f k).val.app V) (e P k V x) =
        e Q k V ((f.f k).val.app (op V.unop.left) x))
    (Fflat : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (_fP : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (P.X n)),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := J.over U) (R := R.over U) (F₀.obj P))
    (r : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
      DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
    (α : DerivedCategory.Q ⋙ r ≅
      F₀ ⋙ DerivedCategory.Q)
    (d : RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{c, v, r, w} J R)
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      r S SU (RingedSliceFlatRestriction.{c, v, r} J R U))
    (hmodel : SliceTensorModelComplex J R U S T SU TU F₀ e Fflat r α d) :
    ∀ X Y Z,
      r.map (S.monoidal.associator X Y Z).hom ≫
        (d.rho X (S.tensor.obj (Y, Z))).hom ≫
        SU.tensor.map
          (X := (r.obj X, r.obj (S.tensor.obj (Y, Z))))
          (Y := (r.obj X, SU.tensor.obj (r.obj Y, r.obj Z)))
          (𝟙 (r.obj X), (d.rho Y Z).hom) =
      (d.rho (S.tensor.obj (X, Y)) Z).hom ≫
        SU.tensor.map
          (X := (r.obj (S.tensor.obj (X, Y)), r.obj Z))
          (Y := (SU.tensor.obj (r.obj X, r.obj Y), r.obj Z))
          ((d.rho X Y).hom, 𝟙 (r.obj Z)) ≫
        (SU.monoidal.associator (r.obj X) (r.obj Y) (r.obj Z)).hom := by
  classical
  let := S.monoidal
  let := SU.monoidal
  unfold SliceTensorModelComplex at hmodel
  choose γModel hγModel heModel using hmodel
  have hsModel := K.associator_model
  have huModel := KU.associator_model
  unfold RingedDerivedTensorAssociatorModel at hsModel huModel
  choose aModel haModel heaModel using hsModel
  choose aUModel haUModel heaUModel using huModel
  have hres (G : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) :
      ∃ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) (f : P ⟶ G),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
        (∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
          (J := J) (R := R) (P.X n)) ∧ QuasiIso f := by
    obtain ⟨P, f, hP, fP, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
    refine ⟨P, f, hP, ?_, hf⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R (P.X n)).symm (fP n)
  choose res resMap resKFlat resFlat resQI using hres
  let F := F₀
  let A := coefficientTotalTensor.{r, c, v} J R
  let AU := coefficientTotalTensor.{r, max c v, v} (J.over U) (R.over U)
  have base (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
      (hN : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) N)
      (fP : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (P.X n))
      (fQ : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (Q.X n))
      (fN : ∀ n, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (N.X n)) :
      r.map (S.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom ≫
        (d.rho (DerivedCategory.Q.obj P)
          (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N))).hom ≫
        SU.tensor.map
          (X := (r.obj (DerivedCategory.Q.obj P),
            r.obj (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N))))
          (Y := (r.obj (DerivedCategory.Q.obj P),
            SU.tensor.obj (r.obj (DerivedCategory.Q.obj Q), r.obj (DerivedCategory.Q.obj N))))
          (𝟙 _, (d.rho (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj N)).hom) =
      (d.rho (S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
          (DerivedCategory.Q.obj N)).hom ≫
        SU.tensor.map
          (X := (r.obj (S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)),
            r.obj (DerivedCategory.Q.obj N)))
          (Y := (SU.tensor.obj (r.obj (DerivedCategory.Q.obj P), r.obj (DerivedCategory.Q.obj Q)),
            r.obj (DerivedCategory.Q.obj N)))
          ((d.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom, 𝟙 _) ≫
        (SU.monoidal.associator (r.obj (DerivedCategory.Q.obj P))
          (r.obj (DerivedCategory.Q.obj Q)) (r.obj (DerivedCategory.Q.obj N))).hom := by
    have hPQ := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ
    have hQN := coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN
    have fPQ := tensor_flat.{c, v, r} J R P Q fP fQ
    have fQN := tensor_flat.{c, v, r} J R Q N fQ fN
    let γPQ := γModel P Q hP hQ fP fQ
    have hγPQ := hγModel P Q hP hQ fP fQ
    have hePQ := heModel P Q hP hQ fP fQ
    let γQN := γModel Q N hQ hN fQ fN
    have hγQN := hγModel Q N hQ hN fQ fN
    have heQN := heModel Q N hQ hN fQ fN
    let γL := γModel (A.obj (P, Q)) N hPQ hN fPQ fN
    have hγL := hγModel (A.obj (P, Q)) N hPQ hN fPQ fN
    have heL := heModel (A.obj (P, Q)) N hPQ hN fPQ fN
    let γR := γModel P (A.obj (Q, N)) hP hQN fP fQN
    have hγR := hγModel P (A.obj (Q, N)) hP hQN fP fQN
    have heR := heModel P (A.obj (Q, N)) hP hQN fP fQN
    let a := aModel P Q N hP hQ hN
    have ha := haModel P Q N hP hQ hN
    have hea := heaModel P Q N hP hQ hN
    let aU := aUModel (F.obj P) (F.obj Q) (F.obj N)
      (Fflat P hP fP) (Fflat Q hQ fQ) (Fflat N hN fN)
    have haU := haUModel (F.obj P) (F.obj Q) (F.obj N)
      (Fflat P hP fP) (Fflat Q hQ fQ) (Fflat N hN fN)
    have heaU := heaUModel (F.obj P) (F.obj Q) (F.obj N)
      (Fflat P hP fP) (Fflat Q hQ fQ) (Fflat N hN fN)
    conv at hea =>
      lhs
      arg 1
      rw [K.tensorIso_both (A.obj (P, Q)) N hPQ hN]
    conv at hea =>
      rhs
      arg 2
      arg 1
      rw [K.tensorIso_both P (A.obj (Q, N)) hP hQN]
    have hc := slice_tensor_associator_square.{c, v, r} J R U
      (tensorPresentation.{c, v, r} J R)
      (tensorPresentation.{max c v, v, r} (J.over U) (R.over U)) F e he
      P Q N a aU γPQ γQN γL γR hγPQ hγQN hγL hγR ha haU
    let PU := F.obj P
    let QU := F.obj Q
    let NU := F.obj N
    have hPU := (Fflat P hP fP)
    have hQU := (Fflat Q hQ fQ)
    have hNU := (Fflat N hN fN)
    have hPQU := coefficientTotalTensor_isKFlat.{r, max c v, v}
      (J.over U) (R.over U) PU QU hPU hQU
    have hQNU := coefficientTotalTensor_isKFlat.{r, max c v, v}
      (J.over U) (R.over U) QU NU hQU hNU
    conv at heaU =>
      lhs
      arg 1
      rw [KU.tensorIso_both (AU.obj (PU, QU)) NU hPQU hNU]
    conv at heaU =>
      rhs
      arg 2
      arg 1
      rw [KU.tensorIso_both PU (AU.obj (QU, NU)) hPU hQNU]
    have hnL := KU.tensorIso_naturality (F.obj (A.obj (P, Q))) NU
      (AU.obj (PU, QU)) NU (Or.inr hNU) (Or.inr hNU) γPQ.hom (𝟙 NU)
    conv at hnL =>
      lhs
      arg 2
      rw [KU.tensorIso_both (AU.obj (PU, QU)) NU hPQU hNU]
    conv at hnL =>
      rhs
      arg 1
      rw [KU.tensorIso_both (F.obj (A.obj (P, Q))) NU
        (Fflat (A.obj (P, Q)) hPQ fPQ) hNU]
    simp only [Functor.map_id] at hnL
    have hnR := KU.tensorIso_naturality PU (F.obj (A.obj (Q, N)))
      PU (AU.obj (QU, NU)) (Or.inl hPU) (Or.inl hPU) (𝟙 PU) γQN.hom
    conv at hnR =>
      lhs
      arg 2
      rw [KU.tensorIso_both PU (AU.obj (QU, NU)) hPU hQNU]
    conv at hnR =>
      rhs
      arg 1
      rw [KU.tensorIso_both PU (F.obj (A.obj (Q, N))) hPU
        (Fflat (A.obj (Q, N)) hQN fQN)]
    simp only [Functor.map_id] at hnR
    dsimp only [tensorPresentation] at hc
    exact associator_of_representative_comparisons S SU d
      DerivedCategory.Q DerivedCategory.Q F A AU α P Q N γPQ γQN γL γR a aU
      (T.iso J R S P Q hP hQ) (T.iso J R S Q N hQ hN)
      (T.iso J R S (A.obj (P, Q)) N hPQ hN)
      (T.iso J R S P (A.obj (Q, N)) hP hQN)
      (TU.iso (J.over U) (R.over U) SU PU QU hPU hQU)
      (TU.iso (J.over U) (R.over U) SU QU NU hQU hNU)
      (TU.iso (J.over U) (R.over U) SU (AU.obj (PU, QU)) NU hPQU hNU)
      (TU.iso (J.over U) (R.over U) SU PU (AU.obj (QU, NU)) hPU hQNU)
      (TU.iso (J.over U) (R.over U) SU (F.obj (A.obj (P, Q))) NU
        (Fflat (A.obj (P, Q)) hPQ fPQ) hNU)
      (TU.iso (J.over U) (R.over U) SU PU (F.obj (A.obj (Q, N)))
        hPU (Fflat (A.obj (Q, N)) hQN fQN))
      hePQ heQN heL heR hea heaU hnL hnR hc
  -- Transport the representative square along the chosen resolving isomorphisms.
  intro X Y Z
  classical
  let P := res (DerivedCategory.Q.objPreimage X)
  let f := resMap (DerivedCategory.Q.objPreimage X)
  have hP := resKFlat (DerivedCategory.Q.objPreimage X)
  have fP := resFlat (DerivedCategory.Q.objPreimage X)
  have hf := resQI (DerivedCategory.Q.objPreimage X)
  let Q := res (DerivedCategory.Q.objPreimage Y)
  let g := resMap (DerivedCategory.Q.objPreimage Y)
  have hQ := resKFlat (DerivedCategory.Q.objPreimage Y)
  have fQ := resFlat (DerivedCategory.Q.objPreimage Y)
  have hg := resQI (DerivedCategory.Q.objPreimage Y)
  let N := res (DerivedCategory.Q.objPreimage Z)
  let v := resMap (DerivedCategory.Q.objPreimage Z)
  have hN := resKFlat (DerivedCategory.Q.objPreimage Z)
  have fN := resFlat (DerivedCategory.Q.objPreimage Z)
  have hv := resQI (DerivedCategory.Q.objPreimage Z)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hg
  have : IsIso (DerivedCategory.Q.map v) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hv
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  let e' := asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso Y
  let e'' := asIso (DerivedCategory.Q.map v) ≪≫ DerivedCategory.Q.objObjPreimageIso Z
  apply associator_of_iso S SU d e e' e''
  exact base P Q N hP hQ hN fP fQ fN

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Normalize localization comparisons without unfolding the tensor construction.
include K KU hd in
/-- The normalized slice tensor comparison preserves the derived associator.
Source: Stacks Tags 07A4 and 0FPT
(blueprint: lem-sfb-ringed-slice-tensor-constraints).

Proof: choose flat-term K-flat representatives for the three arguments. Their total
products again have flat terms and are K-flat. The four tensor comparison squares
identify both sides with restrictions of the two reassociation maps of total complexes.
They agree on every triple of local pure tensors, because tensor restriction sends
pure tensors to the identical pure tensors and reassociation changes no sign.
The universal properties of sheafification, coproducts, and tensor-Hom adjunction
detect this equality. Naturality transports it along resolving quasi-isomorphisms
and the localization comparisons to arbitrary derived objects. -/
theorem ringedSlice_tensor_associator :
    let r := ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U
    ∀ X Y Z,
      r.map (S.monoidal.associator X Y Z).hom ≫
        (d.rho X (S.tensor.obj (Y, Z))).hom ≫
        SU.tensor.map
          (X := (r.obj X, r.obj (S.tensor.obj (Y, Z))))
          (Y := (r.obj X, SU.tensor.obj (r.obj Y, r.obj Z)))
          (𝟙 (r.obj X), (d.rho Y Z).hom) =
      (d.rho (S.tensor.obj (X, Y)) Z).hom ≫
        SU.tensor.map
          (X := (r.obj (S.tensor.obj (X, Y)), r.obj Z))
          (Y := (SU.tensor.obj (r.obj X, r.obj Y), r.obj Z))
          ((d.rho X Y).hom, 𝟙 (r.obj Z)) ≫
        (SU.monoidal.associator (r.obj X) (r.obj Y) (r.obj Z)).hom := by
  dsimp only
  exact sliceTensorModel_associator J R U S T s K SU TU sU KU
    (ringedSliceComplexRestriction.{c, v, r} J R U)
    (sliceSection.{c, v, r} J R U) (slice_map_section.{c, v, r} J R U)
    (fun P hP fP ↦ (d.kflat P hP fP).1)
    (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U)
    (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U) d
    (sliceTensorModel_complex J R U S T SU TU
      (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U)
      (ringedSliceLocalizationIso.{c, v, r, w, w'} J R U) d hd.1)

end CategoryTheory
