/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison

/-!
# Comparison of right derived functors along exact functors, under an acyclicity hypothesis

Let `P : C' ⥤ C` and `E : D' ⥤ D` be exact functors between abelian categories,
`F : C ⥤ D` and `F' : C' ⥤ D'` additive functors and `α : P ⋙ F ≅ F' ⋙ E`. Assume that for
every K-injective complex `I` on `C'` and every quasi-isomorphism `P(I) ⟶ J` to a K-injective
complex `J`, the map `F(P I) ⟶ F(J)` is a quasi-isomorphism (i.e. `P` sends K-injectives to
`F`-acyclic complexes). Then there is a unique isomorphism `D(P) ⋙ RF ≅ RF' ⋙ D(E)` compatible
with the units of the right derived functors and with `α`
(`CategoryTheory.Functor.existsUnique_rightDerivedFunctor_comparison_of_acyclic`).
-/

@[expose] public section

open CategoryTheory Category Limits DerivedCategory

namespace CategoryTheory.Functor

section CompMapDerivedCategory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C]

/-- The comparison `R(F ⋙ G) ≅ RF ⋙ D(G)` for an exact functor `G`, evaluated on the units
`Q(F K) ⟶ RF(Q K)` of cochain complexes. -/
@[reassoc]
lemma rightDerivedFunctorUnitQ_rightDerivedFunctorCompMapDerivedCategoryIso_hom_app
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (F ⋙ G).rightDerivedFunctorUnitQ K ≫
        (rightDerivedFunctorCompMapDerivedCategoryIso F G).hom.app (Q.obj K) =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj K) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ K) := by
  have h (L : CochainComplex D ℤ) :
      (quotientCompQhIso E).inv.app ((G.mapHomologicalComplex _).obj L) ≫
        G.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj L) =
      G.mapDerivedCategoryFactors.inv.app L ≫
        G.mapDerivedCategory.map ((quotientCompQhIso D).inv.app L) := by
    rw [← cancel_mono (G.mapDerivedCategoryFactorsh.hom.app _), assoc, Iso.inv_hom_id_app,
      G.mapDerivedCategoryFactorsh_hom_app]
    simp only [comp_obj, assoc, cancelIso, Iso.inv_hom_id_app_assoc, NatIso.cancel_natIso_inv_left]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    exact (Qh.map_id _).symm
  have n := (rightDerivedFunctorCompMapDerivedCategoryIso F G).hom.naturality
    ((quotientCompQhIso C).hom.app K)
  have h₁ := rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac F G
    ((HomotopyCategory.quotient _ _).obj K)
  rw [rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at h₁
  simp only [rightDerivedFunctorUnitQ, assoc]
  rw [n]
  erw [reassoc_of% h₁, reassoc_of% (h ((F.mapHomologicalComplex _).obj K))]
  simp only [Functor.map_comp]
  rfl

/-- Natural transformations out of `RF ⋙ D(G)`, for an exact functor `G`, are determined by
their compositions with the maps `Q(G(F K)) ≅ D(G)(Q(F K)) ⟶ D(G)(RF(Q K))`. -/
lemma rightDerivedFunctor_comp_mapDerivedCategory_hom_ext (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {H : DerivedCategory C ⥤ DerivedCategory E}
    (γ₁ γ₂ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶ H)
    (h : ∀ K, G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj K) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ K) ≫ γ₁.app (Q.obj K) =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj K) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ K) ≫ γ₂.app (Q.obj K)) :
    γ₁ = γ₂ := by
  rw [← cancel_epi (rightDerivedFunctorCompMapDerivedCategoryIso F G).hom]
  refine rightDerivedFunctor_hom_ext _ _ (fun K ↦ ?_)
  simpa only [NatTrans.comp_app,
    rightDerivedFunctorUnitQ_rightDerivedFunctorCompMapDerivedCategoryIso_hom_app_assoc]
    using h K

end CompMapDerivedCategory

section Comparison

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D] [HasDerivedCategory D']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']

/-- **Comparison of right derived functors along exact functors.** Let `P : C' ⥤ C` and
`E : D' ⥤ D` be exact, `F : C ⥤ D` and `F' : C' ⥤ D'` additive and `α : P ⋙ F ≅ F' ⋙ E`.
If `F` sends every quasi-isomorphism `P(I) ⟶ J` from the image of a K-injective complex `I` to
a K-injective complex `J` to a quasi-isomorphism, then there is a unique isomorphism
`D(P) ⋙ RF ≅ RF' ⋙ D(E)` compatible with the units of `RF`, `RF'` and with `α`.

It is the inverse of the pullback map `R(F' ⋙ E) ⟶ D(P) ⋙ RF` along `α⁻¹`, composed with
`RF' ⋙ D(E) ≅ R(F' ⋙ E)`; it is invertible since on a K-injective complex `I` it is
`F'(I) ⟶ F(P I) ⟶ F(J)` for a K-injective resolution `P(I) ⟶ J`. -/
theorem existsUnique_rightDerivedFunctor_comparison_of_acyclic
    (P : C' ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : C ⥤ D) (F' : C' ⥤ D') (E : D' ⥤ D) [F.Additive] [F'.Additive] [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (α : P ⋙ F ≅ F' ⋙ E)
    (hac : ∀ (I : CochainComplex C' ℤ) [I.IsKInjective] (J : CochainComplex C ℤ)
      [J.IsKInjective] (j : (P.mapHomologicalComplex _).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((F.mapHomologicalComplex _).map j)) :
    ∃! d : P.mapDerivedCategory ⋙ F.rightDerivedFunctor ≅
        F'.rightDerivedFunctor ⋙ E.mapDerivedCategory,
      ∀ K : CochainComplex C' ℤ,
        F.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
            F.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.inv.app K) ≫
            d.hom.app (Q.obj K) =
          Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app K) ≫
            E.mapDerivedCategoryFactors.inv.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) ≫
            E.mapDerivedCategory.map (F'.rightDerivedFunctorUnitQ K) := by
  let δ : F'.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      P.mapDerivedCategory ⋙ F.rightDerivedFunctor :=
    (rightDerivedFunctorCompMapDerivedCategoryIso F' E).inv ≫ rightDerivedPullback P α.inv
  have hδ (K : CochainComplex C' ℤ) :
      E.mapDerivedCategoryFactors.inv.app ((F'.mapHomologicalComplex _).obj K) ≫
        E.mapDerivedCategory.map (F'.rightDerivedFunctorUnitQ K) ≫ δ.app (Q.obj K) =
      Q.map ((NatIso.mapHomologicalComplex α _).inv.app K) ≫
        F.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex _).obj K) ≫
        F.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.inv.app K) := by
    simp only [δ, NatTrans.comp_app]
    rw [← rightDerivedFunctorUnitQ_rightDerivedFunctorCompMapDerivedCategoryIso_hom_app_assoc,
      Iso.hom_inv_id_app_assoc, rightDerivedFunctorUnitQ_rightDerivedPullback_app']
    rfl
  have : IsIso δ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    rw [NatTrans.isIso_app_iff_of_iso δ e]
    suffices IsIso ((rightDerivedPullback P α.inv).app (Q.obj I)) by
      simp only [δ, NatTrans.comp_app]
      infer_instance
    obtain ⟨J, _, j, _, _⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective ((P.mapHomologicalComplex _).obj I)
    have := hac I J j
    have : IsIso ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℤ)).app I) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex α.symm _).app I).hom)
    have k := rightDerivedPullback_app_Q_obj P α.inv I J j
    have : IsIso ((rightDerivedPullback P α.inv).app (Q.obj I) ≫
        F.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app I ≫ Q.map j)) := by
      rw [k]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (F.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app I ≫ Q.map j))
  refine ⟨(asIso δ).symm, fun K ↦ ?_, fun d hd ↦ ?_⟩
  · rw [← cancel_mono (δ.app (Q.obj K))]
    simp only [Iso.symm_hom, asIso_inv, assoc, NatIso.isIso_inv_app, IsIso.inv_hom_id, comp_id]
    rw [hδ, ← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id, id_comp]
  · rw [← Iso.symm_eq_iff, Iso.symm_symm_eq]
    refine Iso.ext ?_
    refine rightDerivedFunctor_comp_mapDerivedCategory_hom_ext F' E _ _ (fun K ↦ ?_)
    rw [Iso.symm_hom, asIso_hom, hδ,
      ← cancel_epi (Q.map ((NatIso.mapHomologicalComplex α _).hom.app K)),
      ← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id, id_comp, ← reassoc_of% (hd K),
      Iso.hom_inv_id_app]
    erw [comp_id]

end Comparison

end CategoryTheory.Functor
