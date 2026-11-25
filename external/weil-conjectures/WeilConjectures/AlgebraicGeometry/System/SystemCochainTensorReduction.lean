/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Tensor compatibility of cochain horizontal reduction adjoints

Source: Zheng Construction 4.1; Stacks 03EK, 06YN, 07A4.
(blueprint: lem-pur-system-cochain-tensor-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] hasDerived SheafOfModules.monoidalCategory evaluation
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The degreewise ordinary horizontal adjoints form a cochain morphism.
Source: Zheng Construction 4.1; Stacks 06YN
(blueprint: lem-pur-system-cochain-tensor-reduction). -/
def cochainReduction (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    ((A.scalar h).model.E.mapHomologicalComplex (.up ℤ)).obj
      (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P where
  f k := ordinaryReduction.{c, v, r} J B τ A h (P.X k)
  comm' k l := by
    intro _
    symm
    change (A.scalar h).model.E.map
        ((evaluation.{c, v, max c v r} J B τ m).map (P.d k l)) ≫
        ordinaryReduction.{c, v, r} J B τ A h (P.X l) =
      ordinaryReduction.{c, v, r} J B τ A h (P.X k) ≫
        (evaluation.{c, v, max c v r} J B τ n).map (P.d k l)
    apply ((A.scalar h).ordinaryAdjunction.homEquiv _ _).injective
    rw [(A.scalar h).ordinaryAdjunction.homEquiv_naturality_left,
      (A.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
    simp only [ordinaryReduction, Equiv.apply_symm_apply]
    exact (transition.{c, v, max c v r} J B τ h).naturality (P.d k l)

private theorem cochainReduction_f (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) (k : ℤ) :
    (cochainReduction.{c, v, r} J B τ A h P).f k =
      ordinaryReduction.{c, v, r} J B τ A h (P.X k) := rfl

/-- The degreewise construction agrees with the induced cochain adjunction.
Source: Stacks 06YN (blueprint: lem-pur-system-cochain-tensor-reduction).
Proof: the inverse Hom equivalence is extension of the map followed by the
counit in both constructions, and the cochain counit is degreewise. -/
theorem cochainReduction_eq_transpose (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    cochainReduction.{c, v, r} J B τ A h P =
      (((A.scalar h).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
        ((NatTrans.mapHomologicalComplex
          (transition.{c, v, max c v r} J B τ h) (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (evaluation.{c, v, max c v r} J B τ n ⋙
              res (coefficientMap J B τ h))) (.up ℤ)).inv.app P) := by
  apply HomologicalComplex.Hom.ext
  funext k
  rw [Adjunction.homEquiv_counit]
  change ordinaryReduction.{c, v, r} J B τ A h (P.X k) = _
  rw [ordinaryReduction, Adjunction.homEquiv_counit]
  rfl

private theorem ordinaryReduction_naturality (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) {M N : Systems.{c, v, max c v r} J B τ} (f : M ⟶ N) :
    (A.scalar h).model.E.map ((evaluation.{c, v, max c v r} J B τ m).map f) ≫
      ordinaryReduction.{c, v, r} J B τ A h N =
    ordinaryReduction.{c, v, r} J B τ A h M ≫
      (evaluation.{c, v, max c v r} J B τ n).map f := by
  apply ((A.scalar h).ordinaryAdjunction.homEquiv _ _).injective
  rw [(A.scalar h).ordinaryAdjunction.homEquiv_naturality_left,
    (A.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
  simp only [ordinaryReduction, Equiv.apply_symm_apply]
  exact (transition.{c, v, max c v r} J B τ h).naturality f

private theorem ordinary_tensor_reduction_inv (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) (M N : Systems.{c, v, max c v r} J B τ) :
    ((A.scalarTensorModel h).ordinary
        ((evaluation.{c, v, max c v r} J B τ m).obj M)
        ((evaluation.{c, v, max c v r} J B τ m).obj N)).inv ≫
      (A.scalar h).model.E.map
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv ≫
      ordinaryReduction.{c, v, r} J B τ A h
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) =
    ordinaryTensorHom.{c, v, r} J (B n)
        (ordinaryReduction.{c, v, r} J B τ A h M)
        (ordinaryReduction.{c, v, r} J B τ A h N) ≫
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv := by
  apply (cancel_mono (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ordinary_tensor_reduction.{c, v, r} J B τ A h M N]
  rw [← (A.scalar h).model.E.map_comp_assoc, Iso.inv_hom_id]
  erw [(A.scalar h).model.E.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]

private theorem tensorSummand_map (R : Sheaf J CommRingCat.{max c v r})
    {P P' Q Q' : CochainComplex (Mod.{c, v, max c v r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q k : ℤ) (hpq : p + q = k) :
    tensorSummand.{c, v, r} J R P Q p q k hpq ≫
      ((totalTensor.{c, v, r} J R).map (Prod.mkHom f g)).f k =
    ordinaryTensorHom.{c, v, r} J R (f.f p) (g.f q) ≫
      tensorSummand.{c, v, r} J R P' Q' p q k hpq := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  change HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q k hpq ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _) (.up ℤ)).f k = _
  have hm : HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _) (.up ℤ) =
    HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ) := by
    simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  rw [hm, HomologicalComplex.ι_mapBifunctorMap]
  change (f.f p ▷ Q.X q) ≫ (P'.X p ◁ g.f q) ≫ _ =
    (f.f p ⊗ₘ g.f q) ≫ _
  rw [tensorHom_def, Category.assoc]
  rfl

/-- Paste the summand comparison squares using only functoriality and associativity. -/
private theorem cochainReduction_summand_paste {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {X₁ X₂ X₃ X₄ : D} {Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ : E}
    {j : X₁ ⟶ X₂} {t : X₂ ⟶ X₄} {v : X₁ ⟶ X₃} {w : X₃ ⟶ X₄}
    {i : Y₁ ⟶ Y₂} {s : Y₂ ⟶ F.obj X₂} {u : Y₁ ⟶ F.obj X₁}
    {r : F.obj X₄ ⟶ Y₅} {a : Y₂ ⟶ Y₄} {b : Y₄ ⟶ Y₅}
    {z : Y₁ ⟶ Y₃} {k : Y₃ ⟶ Y₄} {x : Y₃ ⟶ Y₆} {y : Y₆ ⟶ Y₅}
    {r' : F.obj X₃ ⟶ Y₆}
    (hs : i ≫ s = u ≫ F.map j) (hm : j ≫ t = v ≫ w)
    (hn : k ≫ b = x ≫ y) (hmap : i ≫ a = z ≫ k)
    (hnat : F.map w ≫ r = r' ≫ y) (hinv : u ≫ F.map v ≫ r' = z ≫ x) :
    i ≫ s ≫ F.map t ≫ r = i ≫ a ≫ b := by
  rw [reassoc_of% hs, ← F.map_comp_assoc, hm, F.map_comp, Category.assoc, hnat,
    reassoc_of% hinv, reassoc_of% hmap, hn]

set_option backward.isDefEq.respectTransparency true in
-- The summand calculation compares three dependent ringed module categories.
/-- Cochain reduction commutes with the normalized total tensor comparisons.
Source: Zheng Construction 4.1; Stacks 06YN, 07A4
(blueprint: lem-pur-system-cochain-tensor-reduction).
Proof: test equality in each total degree on every (p,q) summand. The comparison
model summand equations express both maps using the inverse ordinary comparisons.
Naturality moves the horizontal adjoint past the system tensor summand. The
ordinary tensor reduction identity then equates the two remaining maps. This
argument uses every summand of the unbounded total and changes no differential
or Koszul sign. -/
theorem cochain_tensor_reduction (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    (A.scalarTensorModel h).chain
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      ((A.scalar h).model.E.mapHomologicalComplex (.up ℤ)).map
        ((A.tensorEvaluationModel m).chain P Q) ≫
      cochainReduction.{c, v, r} J B τ A h
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).obj (P, Q)) =
    (totalTensor.{c, v, r} J (B n)).map
        (Prod.mkHom (cochainReduction.{c, v, r} J B τ A h P)
          (cochainReduction.{c, v, r} J B τ A h Q)) ≫
      (A.tensorEvaluationModel n).chain P Q := by
  apply HomologicalComplex.Hom.ext
  funext k
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let := SheafOfModules.monoidalCategory (B n)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients (B n)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (B n)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  let Pm := ((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P
  let Qm := ((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q
  have hs := (A.scalarTensorModel h).summand Pm Qm p q k hpq
  have hm := (A.tensorEvaluationModel m).summand P Q p q k hpq
  have hn := (A.tensorEvaluationModel n).summand P Q p q k hpq
  have hmap := tensorSummand_map.{c, v, r} J (B n)
    (cochainReduction.{c, v, r} J B τ A h P)
    (cochainReduction.{c, v, r} J B τ A h Q) p q k hpq
  have hnat := ordinaryReduction_naturality.{c, v, r} J B τ A h
    (tensorSummand.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P Q p q k hpq)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change tensorSummand.{c, v, r} J (B n)
      (((A.scalar h).model.E.mapHomologicalComplex (.up ℤ)).obj Pm)
      (((A.scalar h).model.E.mapHomologicalComplex (.up ℤ)).obj Qm)
      p q k hpq ≫ _ = _
  rw [A.tensorEvaluationModel_ordinary m (P.X p) (Q.X q)] at hm
  rw [A.tensorEvaluationModel_ordinary n (P.X p) (Q.X q)] at hn
  exact cochainReduction_summand_paste (A.scalar h).model.E hs hm hn hmap hnat
    (ordinary_tensor_reduction_inv.{c, v, r} J B τ A h (P.X p) (Q.X q))

end WeilConjectures.SemilinearSections
