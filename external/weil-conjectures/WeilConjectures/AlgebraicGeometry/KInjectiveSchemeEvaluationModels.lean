/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization

/-! # Evaluation with actual models on one scheme site
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-kinjective-scheme-evaluation-models).
There is no site equivalence in this statement: Q is the one localization used
by both ordinary models and the canonical tensor-Hom family.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem ordinaryHomComparison_isIso (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hhom : ∀ (A B : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (t : A ⟶ B),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map t)) :
    IsIso (schemeOrdinaryHomComparison Y P M) := by
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let η := (CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app M
  let t := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map η
  have ht : QuasiIso t := hhom _ _ η
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2
  have : IsIso (DerivedCategory.Q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).2 ht
  unfold schemeOrdinaryHomComparison
  infer_instance

private theorem tensorModel_isIso_right (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (F V : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hV : V.IsKFlatTensor) :
    IsIso (pullbackTensorModelMap Y F V) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let := pullbackDescentModuleTensor Y
  let := moduleSymmetric Y
  have := modulePreadditive Y
  let := moduleClosed Y
  have := moduleGrothendieck Y
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := moduleResolutions Y
  have := moduleDerivedMonoidal Y
  let := pullbackDescentQLax Y
  have hk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj V) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro A hA
    obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hA
    have hr : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj A ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj V) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hV A hA)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
      ((HomotopyCategory.quotient C (.up ℤ)).obj F)
      ((HomotopyCategory.quotient C (.up ℤ)).obj V)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ)) _ _ hk
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) F V) := by
    change IsIso (_ ≫ _ ≫ _)
    change IsIso (_ ≫ (_ ≫ _) ≫ _)
    infer_instance
  change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q F V)
  infer_instance

-- Keep the monoidal transport calculation independent of the concrete derived instances.
private theorem tensorHomEquiv_evaluation_models {C : Type*} [Category* C]
    [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C)
    (e : ∀ A B D : C, (A ⟶ H.obj (op B, D)) ≃ (A ⊗ B ⟶ D))
    (hn : ∀ A A' B B' D D' (x : A' ⟶ A) (y : B' ⟶ B) (z : D ⟶ D')
      (v : A ⟶ H.obj (op B, D)),
      e A' B' D' (x ≫ v ≫ H.map (y.op, z)) = (x ⊗ₘ y) ≫ e A B D v ≫ z)
    {K N V A T B : C} (eN : A ≅ N) (d : V ≅ H.obj (op K, 𝟙_ C))
    (c : B ≅ H.obj (op K, N)) (m : A ⊗ V ≅ T) (f : T ⟶ B)
    (hl : e (N ⊗ V) K N ((eN.inv ▷ V) ≫ m.hom ≫ f ≫ c.hom) =
      (α_ N V K).hom ≫ N ◁ (e V K (𝟙_ C) d.hom) ≫ (ρ_ N).hom) :
    let D := H.obj (op K, 𝟙_ C)
    let g := (e (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁ (e D K (𝟙_ C) (𝟙 D)) ≫ (ρ_ N).hom)
    g ≫ c.inv = (tensorIso eN.symm d.symm ≪≫ m).hom ≫ f := by
  let D := H.obj (op K, 𝟙_ C)
  let g := (e (N ⊗ D) K N).symm
    ((α_ N D K).hom ≫ N ◁ (e D K (𝟙_ C) (𝟙 D)) ≫ (ρ_ N).hom)
  change g ≫ c.inv = _
  have hd := hn D V K K (𝟙_ C) (𝟙_ C) d.hom (𝟙 K) (𝟙 _) (𝟙 D)
  simp only [op_id, ← prod_id', H.map_id, Category.comp_id, tensorHom_id] at hd
  have hg := hn (N ⊗ D) (N ⊗ V) K K N N (N ◁ d.hom) (𝟙 K) (𝟙 N) g
  simp only [op_id, ← prod_id', H.map_id, Category.comp_id, tensorHom_id] at hg
  have heval : e (N ⊗ V) K N ((N ◁ d.hom) ≫ g) =
      (α_ N V K).hom ≫ N ◁ (e V K (𝟙_ C) d.hom) ≫ (ρ_ N).hom := by
    rw [hg]
    dsimp only [g]
    rw [Equiv.apply_symm_apply]
    rw [associator_naturality_middle_assoc, hd, whiskerLeft_comp]
    simp only [Category.assoc]
  have heq := (e (N ⊗ V) K N).injective (heval.trans hl.symm)
  apply (cancel_mono c.hom).1
  apply (cancel_epi (N ◁ d.hom)).1
  simpa [tensorIso_hom, tensorHom_def', Category.assoc, ← whiskerLeft_comp] using heq

/-- Compute derived evaluation using ordinary complexes on the same scheme site.
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ, representative calculation.
(blueprint: lem-pc-kinjective-scheme-evaluation-models).

Proof: resolve the degree-zero unit by the fixed functorial K-injective resolution.
Apply hhom to its resolution map: Hom(P,eta_unit) is a quasi-isomorphism. Compose
its inverse localization with the recorded internal-Hom factorization to identify
the ordinary dual with RHom(K,1), including eK. The same factorization computes
Hom(P,F), because F is already K-injective; compose with eK and eN to obtain b.
K-flatness of the ordinary dual makes the localization tensor comparison invertible.
Use symmetry to put that K-flat dual first, apply kFlat_derivedTensor_comparison_natIso,
and restore the order F tensor dual. Compose with eN and the dual comparison to get a.
For the square, replace the tensor inputs by K-flat resolutions. Use the canonical
representative equation of schemeDerivedTensorHomEquiv with the identity of the
derived dual. On a summand F^p tensor dual^q followed by the r-th Hom projection,
uncurrying this identity and applying the right unitor gives the displayed ordinary
unit-action formula if r+q=0 and zero otherwise. This is hf. The coproduct inclusions
and product projections detect equality of the resulting chain maps. Naturality
with the resolution maps then identifies the localized maps; cancel the localized
Hom-resolution isomorphisms. Finally the canonical family's three-variable
naturality transports along eK and eN. No inverse of f, finite freeness or boundedness
is used. The same equations hold for zero complexes and the empty scheme. -/
theorem exists_kInjective_scheme_evaluation_models (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K N : schemeDerivedCategory Y)
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hhom : ∀ (M M' : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map t))
    (hdual : (homComplex.{u, u, u, u} (R := Y.sheaf) P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))).IsKFlatTensor)
    (eK : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj F ≅ N)
    (f : pullbackTensorTotal Y F
        (homComplex.{u, u, u, u} (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex.{u, u, u, u} (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) [F.IsKInjective] :
    let H := derivedInternalHom (Opens.grothendieckTopology Y.toRingedSpace) Y.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory Y))
    let g := ((schemeDerivedTensorHomEquiv Y) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv Y) D K
          (𝟙_ (schemeDerivedCategory Y)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ DerivedCategory.Q.obj (pullbackTensorTotal Y F
          (homComplex.{u, u, u, u} (R := Y.sheaf) P
            ((HomologicalComplex.single _ (.up ℤ) 0).obj
              (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))))),
      ∃ b : H.obj (op K, N) ≅ DerivedCategory.Q.obj (homComplex.{u, u, u, u} (R := Y.sheaf) P F),
        g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  classical
  let H : (schemeDerivedCategory Y)ᵒᵖ × schemeDerivedCategory Y ⥤
      schemeDerivedCategory Y :=
    derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let V := homComplex.{u, u, u, u} (R := Y.sheaf) P O
  let D := H.obj (op K, 𝟙_ (schemeDerivedCategory Y))
  let c : DerivedCategory.Q.obj (homComplex.{u, u, u, u} (R := Y.sheaf) P F) ⟶
      H.obj (op K, N) := schemeOrdinaryHomComparison Y P F ≫ H.map (eK.inv.op, eN.hom)
  let t : DerivedCategory.Q.obj V ⟶ D := schemeOrdinaryHomComparison Y P O ≫
    H.map (eK.inv.op, ((DerivedCategory.quotientCompQhIso _).app O).inv)
  have := ordinaryHomComparison_isIso Y P F hhom
  have := ordinaryHomComparison_isIso Y P O hhom
  have : IsIso (H.mapIso (eK.symm.op.prod eN)).hom := inferInstance
  have : IsIso (H.mapIso (eK.symm.op.prod
      ((DerivedCategory.quotientCompQhIso _).app O).symm)).hom := inferInstance
  have : IsIso c := by
    dsimp only [c]
    change IsIso (schemeOrdinaryHomComparison Y P F ≫
      (H.mapIso (eK.symm.op.prod eN)).hom)
    infer_instance
  have : IsIso t := by
    dsimp only [t]
    change IsIso (schemeOrdinaryHomComparison Y P O ≫
      (H.mapIso (eK.symm.op.prod
        ((DerivedCategory.quotientCompQhIso _).app O).symm)).hom)
    infer_instance
  let d : DerivedCategory.Q.obj V ≅ D := asIso t
  let b := (asIso c).symm
  have := tensorModel_isIso_right Y F V hdual
  let a := tensorIso eN.symm d.symm ≪≫ asIso (pullbackTensorModelMap Y F V)
  refine ⟨a, b, ?_⟩
  exact tensorHomEquiv_evaluation_models H (schemeDerivedTensorHomEquiv Y)
    (schemeDerivedTensorHomEquiv_naturality Y) eN d (asIso c)
    (asIso (pullbackTensorModelMap Y F V)) (DerivedCategory.Q.map f)
    (schemeOrdinaryEvaluation_localization Y K N P F eK eN f hf)

end AlgebraicGeometry
