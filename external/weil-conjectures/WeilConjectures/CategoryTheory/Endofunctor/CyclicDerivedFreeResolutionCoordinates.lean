/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Free cyclic resolutions with independent derived universes

The already proved chain resolution is localized in the two specified derived categories.
Source: Stacks Tags 0152 and 015F and the normalized free resolution.
(blueprint: lem-sf-cyclic-free-resolution-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- The exact free adjunction in the specified, independently chosen localizations.
Source: Stacks 015F (blueprint: lem-sf-cyclic-free-resolution-coordinates). -/
def cyclicDerivedFreeAdjunction :
    (Free.functor F).mapDerivedCategory ⊣ (forget F).mapDerivedCategory :=
  (Free.adjunction F).mapExactDerivedCategory

/-- Its free-forgetful composite.
Source: the free resolution (blueprint: lem-sf-cyclic-free-resolution-coordinates). -/
abbrev cyclicDerivedFreeFunctor :=
  (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory

/-- Comparison with the termwise free-forgetful composite.
Source: Stacks 015F (blueprint: lem-sf-cyclic-free-resolution-coordinates). -/
def cyclicDerivedFreeComparison (K : CochainComplex (IsoAlgebra F) ℤ) :
    (cyclicDerivedFreeFunctor F).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Free.functor F).mapDerivedCategory.mapIso
      ((forget F).mapDerivedCategoryFactors.app K) ≪≫
    (Free.functor F).mapDerivedCategoryFactors.app
      (((forget F).mapHomologicalComplex (.up ℤ)).obj K)

/-- A normalized free triangle, retaining the summand and SES formulas.
Source: Stacks 0152 and the free resolution
(blueprint: lem-sf-cyclic-free-resolution-coordinates). -/
structure CyclicDerivedFreeResolution where
  theta : ∀ (M : IsoAlgebra F) (n : ℤ), Free.obj F M.carrier n ≅ M.carrier
  d : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F
  theta_eq : ∀ M n, (theta M n).hom = Free.hom M (𝟙 M.carrier) n
  summand : ∀ M n,
    Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map (d.app M) =
      Sigma.ι (Free.obj F M.carrier) n -
        (theta M n ≪≫ (theta M (n - 1)).symm).hom ≫
          Sigma.ι (Free.obj F M.carrier) (n - 1)
  zero : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    (d.mapHomologicalComplex (.up ℤ)).app K ≫
      ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K = 0
  shortExact : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    (ShortComplex.mk ((d.mapHomologicalComplex (.up ℤ)).app K)
      (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K) (zero K)).ShortExact
  differential : cyclicDerivedFreeFunctor F ⟶ cyclicDerivedFreeFunctor F
  delta : 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶
    cyclicDerivedFreeFunctor F ⋙ shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ)
  differential_fac : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    differential.app (DerivedCategory.Q.obj K) ≫ (cyclicDerivedFreeComparison F K).hom =
      (cyclicDerivedFreeComparison F K).hom ≫
        DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app K)
  delta_fac : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
    delta.app (DerivedCategory.Q.obj K) ≫
        (shiftFunctor _ (1 : ℤ)).map (cyclicDerivedFreeComparison F K).hom =
      DerivedCategory.triangleOfSESδ (shortExact K)
  distinguished : ∀ M : DerivedCategory (IsoAlgebra F),
    Triangle.mk (differential.app M) ((cyclicDerivedFreeAdjunction F).counit.app M)
      (delta.app M) ∈ distTriang (DerivedCategory (IsoAlgebra F))

private def cyclicFreeComparisonNatIso :
    DerivedCategory.Q ⋙
        ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory) ≅
      (forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (cyclicDerivedFreeComparison F) (fun f ↦ by
    dsimp [cyclicDerivedFreeComparison]
    erw [Category.assoc, ← (Free.functor F).mapDerivedCategory.map_comp_assoc,
      (forget F).mapDerivedCategoryFactors_hom_naturality,
      (Free.functor F).mapDerivedCategory.map_comp,
      Category.assoc, (Free.functor F).mapDerivedCategoryFactors_hom_naturality]
    rfl)

private lemma cyclicFree_derived_counit (K : CochainComplex (IsoAlgebra F) ℤ) :
    (cyclicDerivedFreeAdjunction F).counit.app (DerivedCategory.Q.obj K) =
      (cyclicDerivedFreeComparison F K).hom ≫
        DerivedCategory.Q.map
          (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K) := by
  let : CatCommSq ((Free.functor F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (Free.functor F).mapDerivedCategory :=
    ⟨(Free.functor F).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((forget F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (forget F).mapDerivedCategory :=
    ⟨(forget F).mapDerivedCategoryFactors.symm⟩
  have h := Adjunction.Localization.η_app
    ((Free.adjunction F).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (Free.functor F).mapDerivedCategory (forget F).mapDerivedCategory K
  have hU : (CatCommSq.iso ((forget F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (forget F).mapDerivedCategory).inv.app K =
      (forget F).mapDerivedCategoryFactors.hom.app K := rfl
  have hI : (CatCommSq.iso ((Free.functor F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Free.functor F).mapDerivedCategory).inv.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) =
      (Free.functor F).mapDerivedCategoryFactors.hom.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) := rfl
  rw [hU, hI] at h
  have hc : ((Free.adjunction F).mapHomologicalComplex (.up ℤ)).counit.app K =
      ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K := by
    ext n
    exact (Free.adjunction F).mapHomologicalComplex_counit_app_f (.up ℤ) K n
  rw [hc] at h
  simpa only [cyclicDerivedFreeAdjunction, Adjunction.mapExactDerivedCategory,
    Adjunction.localization, Adjunction.mkOfUnitCounit, cyclicDerivedFreeComparison,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

omit [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)] in
private theorem cyclicFree_heart :
    ∃ (theta : ∀ (M : IsoAlgebra F) (n : ℤ), Free.obj F M.carrier n ≅ M.carrier)
      (d : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F),
      (∀ M n, (theta M n).hom = Free.hom M (𝟙 M.carrier) n) ∧
      (∀ M n, Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map (d.app M) =
        Sigma.ι (Free.obj F M.carrier) n -
          (theta M n ≪≫ (theta M (n - 1)).symm).hom ≫
            Sigma.ι (Free.obj F M.carrier) (n - 1)) ∧
      ∃ (hz : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
        (d.mapHomologicalComplex (.up ℤ)).app K ≫
          ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K = 0),
      ∀ K : CochainComplex (IsoAlgebra F) ℤ,
        (ShortComplex.mk ((d.mapHomologicalComplex (.up ℤ)).app K)
          (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K)
          (hz K)).ShortExact := by
  let : IsGrothendieckAbelian.{v} (IsoAlgebra F) := isGrothendieckAbelian F
  let : HasDerivedCategory.{v} C := HasDerivedCategory.ofIsGrothendieckAbelian C
  let : HasDerivedCategory.{v} (IsoAlgebra F) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (IsoAlgebra F)
  obtain ⟨theta, d, ht, hd, _, hz, hs, _⟩ := exists_freeDerivedWeilResolution F
  exact ⟨theta, d, ht, hd, hz, hs⟩

/-- The existing free resolution localizes to independent derived universes.
Proof: take the proved termwise resolution, descend its differential and its SES
boundary through fully faithful localization, and identify its counit using the
specified exact adjunction. On representatives the resulting triangle is isomorphic
to the canonical SES triangle. Essential surjectivity gives the result for every object.
Source: Stacks 0152, 015F; free-resolution steps 5--9
(blueprint: lem-sf-cyclic-free-resolution-coordinates). -/
theorem exists_cyclicDerivedFreeResolution : Nonempty (CyclicDerivedFreeResolution F) := by
  obtain ⟨theta, d, ht, hd, hz, hs⟩ := cyclicFree_heart F
  let B := (forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)
  let Q := DerivedCategory.Q (C := IsoAlgebra F)
  let connecting : Q ⟶ (B ⋙ Q) ⋙ shiftFunctor _ (1 : ℤ) :=
    { app K := DerivedCategory.triangleOfSESδ (hs K)
      naturality K L f := by
        let S (K : CochainComplex (IsoAlgebra F) ℤ) :=
          ShortComplex.mk ((d.mapHomologicalComplex (.up ℤ)).app K)
            (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K) (hz K)
        let t : S K ⟶ S L :=
          { τ₁ := B.map f
            τ₂ := B.map f
            τ₃ := f
            comm₁₂ := (d.mapHomologicalComplex (.up ℤ)).naturality f
            comm₂₃ := ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).naturality f }
        exact (DerivedCategory.triangleOfSESδ_naturality (hs K) (hs L) t).symm }
  let A := (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory
  let W := HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ)
  let e : Q ⋙ A ≅ B ⋙ Q := cyclicFreeComparisonNatIso F
  let H := Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory (IsoAlgebra F))
  let dC := d.mapHomologicalComplex (.up ℤ)
  let τ : Q ⋙ A ⟶ Q ⋙ A := e.hom ≫ Functor.whiskerRight dC Q ≫ e.inv
  let dD : A ⟶ A := H.preimage τ
  have hdD (K : CochainComplex (IsoAlgebra F) ℤ) :
      dD.app (Q.obj K) ≫ (e.app K).hom =
        (e.app K).hom ≫ Q.map (dC.app K) := by
    have h := congr_app (H.map_preimage τ) K
    change dD.app (Q.obj K) = (e.app K).hom ≫ Q.map (dC.app K) ≫ (e.app K).inv at h
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id]
    congr 1
    exact Category.comp_id _
  let s := shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ)
  let τδ : Q ⋙ 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶ Q ⋙ (A ⋙ s) :=
    connecting ≫ Functor.whiskerRight e.inv s
  let δ : 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶ A ⋙ s := H.preimage τδ
  have hδ (K : CochainComplex (IsoAlgebra F) ℤ) :
      δ.app (Q.obj K) ≫ s.map (e.app K).hom =
        DerivedCategory.triangleOfSESδ (hs K) := by
    have h := congr_app (H.map_preimage τδ) K
    change δ.app (Q.obj K) =
      DerivedCategory.triangleOfSESδ (hs K) ≫
        s.map (e.app K).inv at h
    rw [h, Category.assoc, ← s.map_comp, Iso.inv_hom_id, s.map_id, Category.comp_id]
  refine ⟨⟨theta, d, ht, hd, hz, hs, dD, δ, hdD, hδ, ?_⟩⟩
  intro K
  let T (K : DerivedCategory (IsoAlgebra F)) :=
    Triangle.mk (dD.app K) ((cyclicDerivedFreeAdjunction F).counit.app K) (δ.app K)
  have hT (L : CochainComplex (IsoAlgebra F) ℤ) : T (Q.obj L) ∈ distTriang _ := by
    apply isomorphic_distinguished _
      (DerivedCategory.triangleOfSES_distinguished (hs L))
    refine Triangle.isoMk _ _ (e.app L) (e.app L) (Iso.refl _) ?_ ?_ ?_
    · change dD.app (Q.obj L) ≫ (e.app L).hom =
        (e.app L).hom ≫ Q.map (dC.app L)
      exact hdD L
    · change (cyclicDerivedFreeAdjunction F).counit.app (Q.obj L) ≫ 𝟙 _ =
        (e.app L).hom ≫ Q.map
          (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app L)
      rw [Category.comp_id]
      exact cyclicFree_derived_counit F L
    · change δ.app (Q.obj L) ≫ s.map (e.app L).hom =
        𝟙 _ ≫ DerivedCategory.triangleOfSESδ (hs L)
      rw [Category.id_comp]
      exact hδ L
  let L := Q.objPreimage K
  let a := Q.objObjPreimageIso K
  apply isomorphic_distinguished _ (hT L)
  refine Triangle.isoMk _ _ (A.mapIso a.symm) (A.mapIso a.symm) a.symm ?_ ?_ ?_
  · exact (dD.naturality a.inv).symm
  · exact ((cyclicDerivedFreeAdjunction F).counit.naturality a.inv).symm
  · exact (δ.naturality a.inv).symm

end CategoryTheory.Endofunctor.IsoAlgebra
