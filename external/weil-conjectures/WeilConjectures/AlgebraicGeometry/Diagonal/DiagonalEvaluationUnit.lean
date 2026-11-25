/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSheafExt

import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # The underlying unit of evaluated simultaneous reduction
Source: diagonal tower system proof, steps (2) and (4).
(blueprint: lem-sfb-diagonal-evaluation-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  diagonalDerivedSingleCounit diagonalScalarExtension diagonalForget diagonalScalarAdjunction

section
variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  {ℓ : ℕ} {L : A ⥤ B} (U : B ⥤ A) [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L) (n : ℕ)

/-- Evaluate a strict system and forget its coefficient action.
Source: diagonal tower system proof, step (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
abbrev diagonalEvaluationForget : (ℕᵒᵖ ⥤ B) ⥤ A :=
  (evaluation ℕᵒᵖ B).obj (op n) ⋙ U

/-- The ordinary quotient unit before deriving it.
Source: diagonal tower system proof, step (2)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
def diagonalEvaluationQuotient : 𝟭 A ⟶ D.ordinary.E ⋙ diagonalEvaluationForget U n :=
  ad.unit ≫ Functor.whiskerRight (D.ordinary.π n) U

/-- A unit of evaluated reduction, normalized on complexes by the universal
counit. This records an actual natural transformation, rather than a collection
of unrelated maps on extension groups. The last field is its degree-zero
specialization, retaining the specified single-complex comparisons.
Source: diagonal tower system proof, steps (2) and (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
structure DiagonalEvaluationUnit where
  unit : 𝟭 (DerivedCategory A) ⟶ D.T ⋙ (diagonalEvaluationForget U n).mapDerivedCategory
  complexes : ∀ K : CochainComplex A ℤ,
    unit.app (DerivedCategory.Q.obj K) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map (D.ε.app K) ≫
        (diagonalEvaluationForget U n).mapDerivedCategoryFactors.hom.app
          ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K ≫
          (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n)
            (.up ℤ)).app K)
  single : ∀ S : A,
    unit.app ((DerivedCategory.singleFunctor A 0).obj S) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map
          (diagonalDerivedSingleCounit ℓ L D S) ≫
        ((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).hom.app
          (D.ordinary.E.obj S) =
      (DerivedCategory.singleFunctor A 0).map
        (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S))

end

section FiniteForgetting
attribute [local semireducible] diagonalForget

/-- Restricting a finite module to p-adic scalars retains its underlying abelian sheaf.
Source: diagonal tower proof, step (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
@[irreducible] def diagonalFiniteForgetIso (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    cartierForget (diagonalResidue.{u} ℓ n) W ≅
      diagonalFiniteToPadic ℓ n W ⋙ diagonalForget ℓ W :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    rfl)

/-- The inverse of the finite forgetting comparison transports an underlying-map
HEq into the corresponding ordinary equality.
Source: diagonal tower proof, step (4)
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
theorem diagonalFiniteForgetIso_transport (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (S : DiagonalAb W)
    (Q : Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (q : S ⟶ (diagonalForget ℓ W).obj ((diagonalFiniteToPadic ℓ n W).obj Q))
    (g : S ⟶ (cartierForget (diagonalResidue.{u} ℓ n) W).obj Q) (h : HEq q g) :
    q ≫ (diagonalFiniteForgetIso ℓ n W).inv.app Q = g := by
  unfold diagonalFiniteForgetIso
  simpa only [NatIso.ofComponents_inv_app, Iso.refl_inv, Category.comp_id] using! eq_of_heq h

end FiniteForgetting

/-- The evaluation left adjoint is exact because every arrow-indexing coproduct is finite.
Source: the evaluation-adjoint argument in diagonal tower proof step (5).
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
private theorem evaluationLeft_exact
    {B : Type*} [Category B] [Abelian B] (n : ℕᵒᵖ) :
    PreservesFiniteLimits (evaluationLeftAdjoint B n) := by
  classical
  have : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  let H := evaluationLeftAdjoint B n
  have (m : ℕᵒᵖ) : PreservesFiniteLimits (H ⋙ (evaluation ℕᵒᵖ B).obj m) := by
    let e : H ⋙ (evaluation ℕᵒᵖ B).obj m ≅
        Functor.const (Discrete (n ⟶ m)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        change Sigma.ι (fun _ : n ⟶ m ↦ X) i ≫
            (Sigma.desc (fun h : n ⟶ m ↦ f ≫ Sigma.ι (fun _ : n ⟶ m ↦ Y) h)) ≫
              𝟙 (∐ fun _ : n ⟶ m ↦ Y) =
          Sigma.ι (fun _ : n ⟶ m ↦ X) i ≫
            𝟙 (∐ fun _ : n ⟶ m ↦ X) ≫
              colimMap ((Functor.const (Discrete (n ⟶ m))).map f)
        simp only [Category.comp_id, Category.id_comp, Sigma.ι_comp_desc]
        exact (ι_colimMap ((Functor.const (Discrete (n ⟶ m))).map f) (Discrete.mk i)).symm)
    exact preservesFiniteLimits_of_natIso e.symm
  exact ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation H J (fun m ↦ inferInstance)⟩

section EvaluationUnitProof
attribute [local semireducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ

/-- A derived right adjoint preserves the universal right Kan extension defining reduction.
Lift the ordinary quotient transformation through this extension; its factorization is the
complexes equation, and naturality of the single-complex comparisons gives the single equation.
Source: diagonal tower system proof steps (2) and (4).
(blueprint: lem-sfb-diagonal-evaluation-unit). -/
private theorem evaluationUnit_of_rightAdjoint
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    {ℓ : ℕ} {L : A ⥤ B} (U : B ⥤ A) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L) (n : ℕ)
    [(diagonalEvaluationForget U n).mapDerivedCategory.IsRightAdjoint] :
    Nonempty (DiagonalEvaluationUnit U ad D n) := by
  let G := diagonalEvaluationForget U n
  let E := D.ordinary.E.mapHomologicalComplex (.up ℤ)
  let q : 𝟭 (CochainComplex A ℤ) ⟶ E ⋙ G.mapHomologicalComplex (.up ℤ) :=
    (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv ≫
      (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n) (.up ℤ)) ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (D.ordinary.E ⋙ G)) (.up ℤ)).inv
  let β : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory A) ⟶
      (E ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory :=
    DerivedCategory.Q.rightUnitor.hom ≫
      Functor.whiskerRight q DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E G.mapDerivedCategoryFactors.inv ≫
      (Functor.associator _ _ _).inv
  let α : DerivedCategory.Q ⋙ (D.T ⋙ G.mapDerivedCategory) ⟶
      (E ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.ε G.mapDerivedCategory
  have := D.universal
  have := D.pointwise
  have : Functor.HasPointwiseRightKanExtension DerivedCategory.Q (E ⋙ DerivedCategory.Q) :=
    Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor _
      DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  have : D.T.IsRightKanExtension D.ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension D.T D.ε
      (HomologicalComplex.quasiIso A (.up ℤ))
  have : (D.T ⋙ G.mapDerivedCategory).IsRightKanExtension α :=
    Functor.PreservesRightKanExtension.preserves D.T D.ε
  let η : 𝟭 (DerivedCategory A) ⟶ D.T ⋙ G.mapDerivedCategory :=
    (D.T ⋙ G.mapDerivedCategory).liftOfIsRightKanExtension α _ β
  have hη (K : CochainComplex A ℤ) :
      η.app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategory.map (D.ε.app K) =
        DerivedCategory.Q.map (q.app K) ≫ G.mapDerivedCategoryFactors.inv.app (E.obj K) := by
    have h := (D.T ⋙ G.mapDerivedCategory).liftOfIsRightKanExtension_fac_app α _ β K
    dsimp only [η, α, β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj] at h ⊢
    simpa only [Category.id_comp, Category.comp_id] using h
  have hcomplex (K : CochainComplex A ℤ) :
      η.app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategory.map (D.ε.app K) ≫
        G.mapDerivedCategoryFactors.hom.app (E.obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K ≫
          (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n)
            (.up ℤ)).app K) := by
    rw [← Category.assoc, hη]
    calc
      _ = DerivedCategory.Q.map (q.app K) := by
        rw [Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
      _ = _ := by
        congr 1
        ext i
        simp only [q, NatTrans.comp_app, HomologicalComplex.comp_f]
        simp only [Functor.mapHomologicalComplexCompIso_inv_app_f,
          Functor.mapHomologicalComplexIdIso_inv_app_f,
          NatTrans.mapHomologicalComplex_app_f]
        change (𝟙 (K.X i)) ≫ (diagonalEvaluationQuotient U ad D n).app (K.X i) ≫
            𝟙 (G.obj (D.ordinary.E.obj (K.X i))) =
          (𝟙 (K.X i)) ≫ (diagonalEvaluationQuotient U ad D n).app (K.X i)
        exact congrArg (fun z ↦ (𝟙 (K.X i)) ≫ z)
          (Category.comp_id ((diagonalEvaluationQuotient U ad D n).app (K.X i)))
  refine ⟨⟨η, hcomplex, ?_⟩⟩
  intro S
  let K := (CochainComplex.singleFunctor A 0).obj S
  let e : E.obj K ⟶ (CochainComplex.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj
      (D.ordinary.E.obj S) :=
    (HomologicalComplex.singleMapHomologicalComplex D.ordinary.E (.up ℤ) 0).hom.app S
  let t : (G.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj S)) ⟶
      (CochainComplex.singleFunctor A 0).obj (G.obj (D.ordinary.E.obj S)) :=
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (D.ordinary.E.obj S)
  have hG : G.mapDerivedCategory.map (DerivedCategory.Q.map e) ≫
      G.mapDerivedCategory.map
        ((DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj S)) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (D.ordinary.E.obj S) =
      G.mapDerivedCategoryFactors.hom.app (E.obj K) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map e ≫ t) ≫
        (DerivedCategory.singleFunctorIsoCompQ A 0).inv.app
          (G.obj (D.ordinary.E.obj S)) := by
    simp only [Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, Category.id_comp]
    erw [← G.mapDerivedCategory.map_comp_assoc
      ((DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj S))
      ((DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).hom.app (D.ordinary.E.obj S)),
      Iso.inv_hom_id_app, G.mapDerivedCategory.map_id, Category.id_comp]
    change G.mapDerivedCategory.map (DerivedCategory.Q.map e) ≫
        G.mapDerivedCategoryFactors.hom.app _ ≫
          (DerivedCategory.Q.map t ≫
            (DerivedCategory.singleFunctorIsoCompQ A 0).inv.app
              (G.obj (D.ordinary.E.obj S))) = _
    erw [G.mapDerivedCategoryFactors_hom_naturality_assoc, ← DerivedCategory.Q.map_comp_assoc]
  have hq :
      ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K ≫
          (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n)
            (.up ℤ)).app K) ≫
        (G.mapHomologicalComplex (.up ℤ)).map e ≫ t =
      (CochainComplex.singleFunctor A 0).map
        (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S)) := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      change ((𝟙 (K.X 0)) ≫ (diagonalEvaluationQuotient U ad D n).app (K.X 0)) ≫
          G.map (e.f 0) ≫ t.f 0 =
        ((HomologicalComplex.single A (.up ℤ) 0).map
          (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S))).f 0
      dsimp only [K, e, t, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self]
      let b := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (D.ordinary.E.obj S)
      have hn := (diagonalEvaluationQuotient U ad D n).naturality
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S).hom
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      simp only [Category.id_comp, Functor.map_comp, Category.assoc]
      erw [← G.map_comp_assoc b.inv b.hom, b.inv_hom_id, G.map_id, Category.id_comp,
        ← reassoc_of% hn]
      simp only [diagonalEvaluationQuotient, NatTrans.comp_app,
        Functor.whiskerRight_app, Category.assoc]
      rfl
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S i hi).eq_of_src _ _
  simp only [diagonalDerivedSingleCounit, Functor.map_comp, Category.assoc]
  change η.app ((DerivedCategory.singleFunctor A 0).obj S) ≫
    G.mapDerivedCategory.map
      (D.T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app S)) ≫
    G.mapDerivedCategory.map (D.ε.app K) ≫
    G.mapDerivedCategory.map (DerivedCategory.Q.map e) ≫
    G.mapDerivedCategory.map
      ((DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj S)) ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app (D.ordinary.E.obj S) = _
  rw [hG]
  have hn := η.naturality ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app S)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% hcomplex K, ← DerivedCategory.Q.map_comp_assoc, hq]
  erw [← (DerivedCategory.singleFunctorIsoCompQ A 0).hom.naturality_assoc
    (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S)),
    Iso.hom_inv_id_app, Category.comp_id]
  simp only [Functor.map_comp]

end EvaluationUnitProof

/-- Evaluating simultaneous reduction has its quotient-normalized underlying unit.

Source: diagonal tower system proof, steps (2) and (4)
(blueprint: lem-sfb-diagonal-evaluation-unit).

Proof: resolve an abelian-sheaf complex by a termwise flat K-flat complex P.
Scalar extension to the constant p-adic ring is flat. Reduction at level n is
computed by P tensor Z/ell^(n+1), and the integral quotient map gives its unit.
The universal left-derived counit is invertible on P. Compose its inverse with
the quotient map, using the exact evaluation-and-forgetting comparison.
Comparison maps of K-flat resolutions commute with the quotient maps; their
quasi-isomorphisms remain quasi-isomorphisms after reduction. Thus these maps
descend to a natural transformation on the unbounded derived category.
Computing on a resolution of any K and using naturality of the universal
counit proves the complexes equation. Specialize to the single complex of S
and insert the single-complex comparison isomorphisms to obtain single.
On K-flat representatives the counit is invertible, so complexes determines
the unit there; essential surjectivity of such representatives gives uniqueness.
Neither Kummer exactness nor any choice of a roots system is involved. -/
theorem diagonal_evaluation_unit_exists (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) (n : ℕ) :
    Nonempty (DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) := by
  -- Construct the unit by the preserved universal right Kan extension.
  have : PreservesFiniteLimits (diagonalScalarExtension ℓ W) := scalarExtension_exact ℓ W
  have : PreservesFiniteColimits (diagonalScalarExtension ℓ W) := by
    have := (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
    infer_instance
  have : (diagonalScalarExtension ℓ W).Additive := scalarExtension_additive ℓ W
  let H := evaluationLeftAdjoint (DiagonalMod ℓ W) (op n)
  have : PreservesFiniteLimits H := evaluationLeft_exact (op n)
  have : H.IsLeftAdjoint := (evaluationAdjunctionRight (DiagonalMod ℓ W) (op n)).isLeftAdjoint
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  let ad := (diagonalScalarAdjunction ℓ W).comp
    (evaluationAdjunctionRight (DiagonalMod ℓ W) (op n))
  have : (diagonalEvaluationForget (diagonalForget ℓ W) n).mapDerivedCategory.IsRightAdjoint :=
    ad.onDerivedCategory.isRightAdjoint
  exact evaluationUnit_of_rightAdjoint (diagonalForget ℓ W) (diagonalScalarAdjunction ℓ W) D n

end AlgebraicGeometry.ProEtale
