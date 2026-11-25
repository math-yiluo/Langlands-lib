/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality of uncurrying on tensor summands
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local irreducible] homComplexFunctor
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem map_id_app_comp {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (H : A ⥤ B ⥤ D) (X : A) (Y Y' : B) (g : Y ⟶ Y') :
    (H.map (𝟙 X)).app Y ≫ (H.obj X).map g = (H.obj X).map g := by
  rw [H.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

private theorem uncurry_natural {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A T T' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (i : T' ⟶ T) (g : T ⟶ SheafOfModules.homObj A N)
    (g' : T ⟶ SheafOfModules.homObj A N') (e : N ⟶ N')
    (h : g' = g ≫ SheafOfModules.homObjMap (𝟙 A) e) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    i ▷ A ≫ (β_ T A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A T N').symm g' =
      (β_ T' A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A T' N).symm (i ≫ g) ≫ e := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  rw [BraidedCategory.braiding_naturality_left_assoc]
  apply congrArg (fun t ↦ (β_ T' A).hom ≫ t)
  apply (SheafOfModules.tensorHomEquiv (R := R) A T' N').injective
  rw [SheafOfModules.tensorHomEquiv_whiskerLeft_comp,
    SheafOfModules.tensorHomEquiv_comp_homObjMap]
  simp only [Equiv.apply_symm_apply, h, Category.assoc]

attribute [local semireducible] homComplexFunctor

private theorem component_formula (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h : q + p = n) :
    schemeTensorHomUncurryComponent X P L M φ p q n h =
      (β_ (P.X p) (L.X q)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := X.sheaf) (L.X q) (P.X p)
          (((schemeHomKInjectiveResolution X).obj M).X n)).symm
          (φ.f p ≫ (Classical.choose
            (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf))) L
              ((schemeHomKInjectiveResolution X).obj M) p q n h) := by
  rfl

attribute [local irreducible] homComplexFunctor

-- The abstract API avoids unfolding Hom-complex data during the calculation.
/-- Restricting uncurrying and postcomposition to an arbitrary tensor summand.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, step 3, naturality portion.
(blueprint: lem-pc-scheme-uncurry-summand-naturality).

Proof: Apply schemeTensorHomUncurry_component to the outer inclusion in degrees
n,r,k. Its inverse tensor-Hom expression uses the projection of Hom(P,I(F)).
The naturality equation of homComplex_projections_exists with identity on P and
eta_F on F moves this projection across Hom(P,eta_F). Naturality of uncurrying in
its target moves eta_F to the last factor. Naturality of the symmetric braiding
and of uncurrying in its source then moves the inner tensor inclusion into the
argument of tensorHomEquiv.symm. Reassociate composition to obtain the displayed
formula. Only n+r=k is used for the Hom projection; p+q=n indexes the inclusion.
This argument imposes no boundedness or nonvanishing hypotheses and works for
zero complexes and the empty scheme. -/
theorem schemeTensorHomUncurry_summand_naturality (Y : Scheme.{u})
    (P F V : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F V ⟶ homComplex (R := Y.sheaf) P F)
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ HomologicalComplex.ιMapBifunctor (pullbackTensorTotal Y F V) P
        (curriedTensor _) (.up ℤ) n r k hnr ≫
          (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F
            (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))).f k =
    (β_ (F.X p ⊗ V.X q) (P.X r)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (F.X p ⊗ V.X q)
        (F.X k)).symm
        (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ≫
          f.f n ≫ π P F n r k (by omega)) ≫ (eta.app F).f k := by
  classical
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
  dsimp only
  have hc := schemeTensorHomUncurry_component Y (pullbackTensorTotal Y F V) P F
    (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))
    n r k hnr (by omega)
  refine (congrArg (fun t ↦
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ t) (hc.trans (component_formula Y (pullbackTensorTotal Y F V) P F
        (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))
        n r k (by omega)))).trans ?_
  dsimp only [HomologicalComplex.comp_f]
  have hn := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))).2.2
      P P F ((schemeHomKInjectiveResolution Y).obj F) (𝟙 P) (eta.app F) n r k
        (by omega)
  have hi := map_id_app_comp (homComplexFunctor (R := Y.sheaf)) (op P) F
    ((schemeHomKInjectiveResolution Y).obj F) (eta.app F)
  have hn' := (congrArg (fun t ↦ t.f n ≫
    π P ((schemeHomKInjectiveResolution Y).obj F) n r k (by omega)) hi).symm.trans hn
  exact uncurry_natural Y.sheaf (P.X r) ((pullbackTensorTotal Y F V).X n)
    (F.X p ⊗ V.X q) (F.X k) (((schemeHomKInjectiveResolution Y).obj F).X k)
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq)
    (f.f n ≫ π P F n r k (by omega))
    ((f.f n ≫ (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F)).f n) ≫
      π P ((schemeHomKInjectiveResolution Y).obj F) n r k (by omega))
    ((eta.app F).f k) ((Category.assoc _ _ _).trans
      ((congrArg (fun t ↦ f.f n ≫ t) hn').trans (Category.assoc _ _ _).symm))

end AlgebraicGeometry
