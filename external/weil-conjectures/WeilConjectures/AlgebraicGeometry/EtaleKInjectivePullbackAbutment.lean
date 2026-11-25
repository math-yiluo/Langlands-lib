/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.EtaleKInjectiveUnitLeray

/-! # K-injective computation of the étale pullback abutment

Source: Stacks Project, Tags 015J, 015K, 070I and 08BJ.
(blueprint: lem-weil-pbc-kinjective-pullback-abutment).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Elaborating resolution and spectral-page comparison families together.
/-- A pullback comparison between K-injective resolutions computes the canonical
unit--Leray map, after the canonical resolution identifications.
Source: Stacks Project, Tag 015J (computation by an injective total resolution),
Tag 015K (independence of comparison maps), and Tags 070I and 08BJ
(K-injective comparison and direct image).
(blueprint: lem-weil-pbc-kinjective-pullback-abutment).

Proof: Apply the underived adjunction to the comparison j to obtain a map
I -> f_* J. Its composite with the resolution of K is homotopic to the
adjoint of v followed by the resolution of L. Pushforward preserves
K-injectives because its left adjoint is exact. Thus this adjoint comparison
computes the derived unit followed by Rf_*(v). Apply RΓ_X and the Leray
isomorphism RΓ_X Rf_* ≅ RΓ_Y. On K-injective complexes their defining units
are isomorphisms and naturality identifies the resulting map with Γ applied
to the adjoint comparison, or equivalently the degreewise unit followed by
Γ_Y(j). This is w by its component formula. Homotopic maps have equal maps
in the derived category. Finally apply H^n and the canonical resolution
isomorphisms; their factors are exactly resolutionEtaleCohomologyIso. -/
theorem etaleKInjective_pullback_abutment
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ)
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L)
    (ρ : CochainComplex.KInjectiveResolutionChoice K)
    (σ : CochainComplex.KInjectiveResolutionChoice L)
    (j : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ρ.complex ⟶ σ.complex)
    (hj : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ρ.map ≫ j) (v ≫ σ.map)))
    (w : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ρ.complex ⟶
        ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj σ.complex)
    (hw : ∀ i : ℤ, w.f i =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (ρ.complex.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (j.f i))
    (n : ℤ) :
    (@resolutionEtaleCohomologyIso.{uNatural} X K ρ.complex ρ.map
        ρ.quasiIso ρ.isKInjective n).inv ≫ HomologicalComplex.homologyMap w n ≫
      (@resolutionEtaleCohomologyIso.{uNatural} Y L σ.complex σ.map
        σ.quasiIso σ.isKInjective n).hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n).map
        ((rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} X).map
            ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app
              (DerivedCategory.Q.obj K)) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{uNatural + 1} f).hom.app
              ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj K)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{uNatural + 1} Y).map
            ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
              DerivedCategory.Q.map v)) := by
  have : ρ.complex.IsKInjective := ρ.isKInjective
  have : σ.complex.IsKInjective := σ.isKInjective
  have : QuasiIso ρ.map := ρ.quasiIso
  have : QuasiIso σ.map := σ.quasiIso
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let H := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let U := (upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategory
  let adj := mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f
  let e := rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    AddCommGrpCat.{uNatural + 1} f
  let β : G.rightDerivedFunctor ⟶ U ⋙ H.rightDerivedFunctor :=
    (Functor.leftUnitor G.rightDerivedFunctor).inv ≫
      Functor.whiskerRight adj.unit G.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft U e.hom
  let a := G.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map ρ.map)) ≪≫
    G.rightDerivedFunctorObjQIso ρ.complex
  let b := H.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map σ.map)) ≪≫
    H.rightDerivedFunctorObjQIso σ.complex
  have hunit : (G.rightDerivedFunctorObjQIso ρ.complex).hom ≫ DerivedCategory.Q.map w ≫
    (H.rightDerivedFunctorObjQIso σ.complex).inv =
      β.app (DerivedCategory.Q.obj ρ.complex) ≫
        H.rightDerivedFunctor.map
          ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app
            ρ.complex ≫ DerivedCategory.Q.map j)  := by
    simpa only [β, G, H, U, adj, e, rightDerivedGlobalSections, NatTrans.comp_app,
      Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id, Category.assoc]
      using etaleKInjective_unit_leray f ρ.complex σ.complex j w hw
  have hq := DerivedCategory.Q_map_eq_of_homotopy _ hj.some
  have hfac := Functor.mapDerivedCategoryFactors_hom_naturality
    (upperStar AddCommGrpCat.{uNatural + 1} f) ρ.map
  have hnat := β.naturality (DerivedCategory.Q.map ρ.map)
  dsimp only [Functor.comp_map] at hnat
  have ht : a.hom ≫ DerivedCategory.Q.map w ≫ b.inv =
      β.app (DerivedCategory.Q.obj K) ≫ H.rightDerivedFunctor.map
        ((upperStar AddCommGrpCat.{uNatural + 1} f).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map v) := by
    dsimp only [a, b, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, asIso_hom, asIso_inv]
    simp only [Category.assoc]
    rw [reassoc_of% hunit, reassoc_of% hnat]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    congr 1
    simp only [Category.assoc]
    rw [reassoc_of% hfac]
    rw [← Functor.map_comp_assoc, hq, Functor.map_comp]
    simp
  let T := DerivedCategory.homologyFunctor AddCommGrpCat.{uNatural + 1} n
  let c := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{uNatural + 1} n).app
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj ρ.complex)
  let d := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{uNatural + 1} n).app
    ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj σ.complex)
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality w n
  change T.map (DerivedCategory.Q.map w) ≫ d.hom =
    c.hom ≫ HomologicalComplex.homologyMap w n at hn
  change (T.mapIso a ≪≫ c).hom ≫ HomologicalComplex.homologyMap w n ≫
    (T.mapIso b ≪≫ d).inv = _
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc]
  rw [← Category.assoc c.hom, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ht]
  simp only [β, G, H, U, adj, e, T, rightDerivedGlobalSections, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]

end AlgebraicGeometry.Etale
