/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionTensorCore.SemilinearTensorReductionCore
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSingletonEvaluationMate
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarTensor
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence

/-! # Below-level factorization of the singleton projection

## References

* Zheng, Construction 4.1 (printed p. 21), Lemma 4.10 and Proposition 4.17(a)
  (printed pp. 25--26)
* Stacks Project, Tags 06YS, 07A4 and 08J9
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
section CategoricalFactorization
universe a a' b b' d d'
variable {X : Type a} [Category.{a'} X] {Y : Type b} [Category.{b'} Y]
  {Z : Type d} [Category.{d'} Z]

private theorem factorization_of_tensor_reduction
    (E : X ⥤ Y) (F : X ⥤ Z) (S : Y ⥤ Z) (L : Y ⥤ X) (adj : L ⊣ E)
    (T : X × X ⥤ X) (U : Y × Y ⥤ Y) (V : Z × Z ⥤ Z)
    (μ : T ⋙ E ≅ E.prod E ⋙ U) (ν : T ⋙ F ≅ F.prod F ⋙ V)
    (γ : U ⋙ S ≅ S.prod S ⋙ V) (δ : E ⋙ S ⟶ F)
    (κ : S ≅ L ⋙ F)
    (hκ : ∀ P, κ.hom.app P = S.map (adj.unit.app P) ≫ δ.app (L.obj P))
    (hδ : ∀ N M, δ.app (T.obj (N, M)) ≫ ν.hom.app (N, M) =
      S.map (μ.hom.app (N, M)) ≫ γ.hom.app (E.obj N, E.obj M) ≫
        V.map (Prod.mkHom (δ.app N) (δ.app M)))
    (M : X) (P : Y) :
    ∃ α : F.obj (L.obj (U.obj (P, E.obj M))) ≅
        V.obj (F.obj (L.obj P), S.obj (E.obj M)),
      F.map ((adj.homEquiv _ _).symm
          (U.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M))) ≫
            μ.inv.app (L.obj P, M))) ≫ ν.hom.app (L.obj P, M) =
        α.hom ≫ V.map (Prod.mkHom (𝟙 (F.obj (L.obj P))) (δ.app M)) := by
  let u := U.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M))) ≫
    μ.inv.app (L.obj P, M)
  let f := (adj.homEquiv _ _).symm u
  let α := κ.symm.app (U.obj (P, E.obj M)) ≪≫ γ.app (P, E.obj M) ≪≫
    V.mapIso ((κ.app P).prod (Iso.refl (S.obj (E.obj M))))
  refine ⟨α, ?_⟩
  change F.map f ≫ ν.hom.app (L.obj P, M) = _
  apply (cancel_epi (κ.hom.app (U.obj (P, E.obj M)))).1
  have hf : κ.hom.app (U.obj (P, E.obj M)) ≫ F.map f =
      S.map u ≫ δ.app (T.obj (L.obj P, M)) := by
    rw [hκ, Category.assoc, ← δ.naturality]
    dsimp only [Functor.comp_map]
    have hu : adj.unit.app (U.obj (P, E.obj M)) ≫ E.map f = u := by
      exact (adj.homEquiv _ _).apply_symm_apply u
    rw [← S.map_comp_assoc, hu]
  rw [← Category.assoc, hf, Category.assoc, hδ]
  have hn := γ.hom.naturality (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M)))
  change S.map (U.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M)))) ≫
      γ.hom.app (E.obj (L.obj P), E.obj M) =
    γ.hom.app (P, E.obj M) ≫
      V.map (Prod.mkHom (S.map (adj.unit.app P)) (S.map (𝟙 (E.obj M)))) at hn
  have hc : S.map u ≫ S.map (μ.hom.app (L.obj P, M)) =
      S.map (U.map (Prod.mkHom (adj.unit.app P) (𝟙 (E.obj M)))) := by
    rw [← S.map_comp]
    simp only [u, Category.assoc, μ.inv_hom_id_app]
    exact congrArg S.map (Category.comp_id _)
  rw [← Category.assoc (S.map u), hc, reassoc_of% hn]
  simp only [α, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.refl_hom, Iso.app_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← V.map_comp, prod_comp, Category.id_comp, ← hκ]
  apply congrArg (fun f ↦ γ.hom.app (P, E.obj M) ≫ V.map f)
  apply Prod.hom_ext
  · exact (Category.comp_id _).symm
  · exact (congrArg (fun f ↦ f ≫ δ.app M) (S.map_id _)).trans (Category.id_comp _)

end CategoricalFactorization

namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Below its source vertex the singleton projection is tensor with the actual
reduction, after scalar/tensor reassociation, for an arbitrary system (no cartesianness or
invertibility of its reduction is assumed). -/
theorem semilinearProjectionBelowFactorization
    (closed : Closed.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    (models : Models.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) closed)
    (level : ∀ n : ℕ, Closed.{c, v, r} J (B n))
    (levelModels : ∀ n : ℕ, Models.{c, v, r} J (B n) (level n))
    (tensorEvaluation : ∀ n : ℕ,
      closed.tensor ⋙ e.{c, v, max c v r} J B τ n ≅
        ((e.{c, v, max c v r} J B τ n).prod
          (e.{c, v, max c v r} J B τ n)) ⋙ (level n).tensor)
    (tensorModel : ∀ n : ℕ,
      TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J) J
        (systemRing.{c, v, max c v r} J B τ) (B n)
        (evaluation.{c, v, max c v r} J B τ n) closed (level n) models
        (levelModels n) (tensorEvaluation n))
    (ordinary : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
      (tensorModel n).ordinary M N = ordinaryEvaluationTensor.{c, v, r} J B τ n M N)
    (M : DS.{c, v, max c v r} J B τ) (n q : ℕ) (h : q ≤ n)
    (A : ScalarData.{c, v, max c v r}
      (coefficientMap.{c, v, max c v r} J B τ h))
    (L : D.{c, v, max c v r} J (B n) ⥤ DS.{c, v, max c v r} J B τ)
    (adj : L ⊣ e.{c, v, max c v r} J B τ n)
    (P : D.{c, v, max c v r} J (B n)) :
    ∃ α : (e.{c, v, max c v r} J B τ q).obj
        (L.obj ((level n).tensor.obj (P, (e.{c, v, max c v r} J B τ n).obj M))) ≅
      (level q).tensor.obj
        ((e.{c, v, max c v r} J B τ q).obj (L.obj P),
          A.T.obj ((e.{c, v, max c v r} J B τ n).obj M)),
      (e.{c, v, max c v r} J B τ q).map
          ((adj.homEquiv _ _).symm
            ((level n).tensor.map
                (Prod.mkHom (adj.unit.app P)
                  (𝟙 ((e.{c, v, max c v r} J B τ n).obj M))) ≫
              (tensorEvaluation n).inv.app (L.obj P, M))) ≫
        (tensorEvaluation q).hom.app (L.obj P, M) =
      α.hom ≫ (level q).tensor.map
        (Prod.mkHom (𝟙 ((e.{c, v, max c v r} J B τ q).obj (L.obj P)))
          (reduction.{c, v, max c v r} J B τ h A M)) := by
  classical
  let scalar : ∀ {m n : ℕ} (h : n ≤ m),
      ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) :=
    fun h ↦ (scalarData_nonempty.{c, v, r} J (coefficientMap J B τ h)).some
  let γ {m n : ℕ} (h : n ≤ m) :=
    (semilinearScalarTensor.{c, v, r} J (B m) (B n) (coefficientMap J B τ h)
      (scalar h) (level m) (level n) (levelModels m) (levelModels n)).choose
  let γmodel {m n : ℕ} (h : n ≤ m) :=
    ((semilinearScalarTensor.{c, v, r} J (B m) (B n) (coefficientMap J B τ h)
      (scalar h) (level m) (level n) (levelModels m) (levelModels n)).choose_spec).some
  let δ : e.{c, v, max c v r} J B τ n ⋙ (scalar h).T ⟶
      e.{c, v, max c v r} J B τ q := {
    app N := reduction.{c, v, max c v r} J B τ h (scalar h) N
    naturality N N' f := by
      apply ((scalar h).adjunction.homEquiv _ _).injective
      dsimp only [Functor.comp_map]
      rw [(scalar h).adjunction.homEquiv_naturality_left,
        (scalar h).adjunction.homEquiv_naturality_right]
      simp only [reduction, Equiv.apply_symm_apply]
      exact (derivedTransition J B τ h).naturality f
  }
  let k : (scalar h).T ⟶ L ⋙ e.{c, v, max c v r} J B τ q := {
    app P := (scalar h).T.map (adj.unit.app P) ≫ δ.app (L.obj P)
    naturality P Q f := by
      change (scalar h).T.map f ≫ (scalar h).T.map (adj.unit.app Q) ≫ δ.app (L.obj Q) = _
      rw [← (scalar h).T.map_comp_assoc]
      have hu := adj.unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      have hd := δ.naturality (L.map f)
      dsimp only [Functor.comp_map] at hd
      rw [hu, (scalar h).T.map_comp, Category.assoc, hd]
      dsimp only [Functor.comp_map]
      exact (Category.assoc _ _ _).symm
  }
  have hk (P : D.{c, v, max c v r} J (B n)) : IsIso (k.app P) :=
    semilinearSingletonEvaluationMate_isIso.{c, v, r} J B τ n q h (scalar h) L adj P
  let κ : (scalar h).T ≅ L ⋙ e.{c, v, max c v r} J B τ q :=
    NatIso.ofComponents (fun P ↦ asIso (k.app P)) (fun f ↦ k.naturality f)
  obtain ⟨α, hα⟩ := factorization_of_tensor_reduction
    (e.{c, v, max c v r} J B τ n) (e.{c, v, max c v r} J B τ q) (scalar h).T L adj
    closed.tensor (level n).tensor (level q).tensor
    (tensorEvaluation n) (tensorEvaluation q) (γ h) δ κ (fun _ ↦ rfl)
    (fun N M ↦ ProjectionTensorCore.semilinearTensorReductionFromModels.{c, v, r} J B τ {
      scalar := scalar
      closed := closed
      tensorModels := models
      levelClosed := level
      levelTensorModels := levelModels
      tensorEvaluation := tensorEvaluation
      tensorEvaluationModel := tensorModel
      tensorEvaluationModel_ordinary := ordinary
      scalarTensor := @γ
      scalarTensorModel := @γmodel } N M h) M P
  let i := (scalar h).adjunction.leftAdjointUniq A.adjunction
  have hr : reduction.{c, v, max c v r} J B τ h (scalar h) M =
      i.hom.app ((e.{c, v, max c v r} J B τ n).obj M) ≫
        reduction.{c, v, max c v r} J B τ h A M := by
    apply ((scalar h).adjunction.homEquiv _ _).injective
    rw [(scalar h).adjunction.homEquiv_naturality_right,
      (scalar h).adjunction.homEquiv_leftAdjointUniq_hom_app A.adjunction]
    change ((scalar h).adjunction.homEquiv _ _)
        (((scalar h).adjunction.homEquiv _ _).symm ((derivedTransition J B τ h).app M)) = _
    rw [Equiv.apply_symm_apply]
    change (derivedTransition J B τ h).app M =
      A.adjunction.unit.app _ ≫ (resD (coefficientMap J B τ h)).map (reduction J B τ h A M)
    exact ((A.adjunction.homEquiv _ _).apply_symm_apply
      ((derivedTransition J B τ h).app M)).symm
  refine ⟨α ≪≫ (level q).tensor.mapIso
    ((Iso.refl _).prod (i.app ((e.{c, v, max c v r} J B τ n).obj M))), ?_⟩
  rw [hα]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
    Category.assoc, ← Functor.map_comp, prod_comp, Category.comp_id, ← hr]
  rfl

end WeilConjectures.SemilinearSections
