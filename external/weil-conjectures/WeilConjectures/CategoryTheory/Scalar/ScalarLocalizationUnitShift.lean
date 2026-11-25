/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Shift coherence of the normalized derived localization unit

Source: Stacks Project, algebra.tex, Tag 00CM (section-localization), and
sites-modules.tex, Tags 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-unit-shift)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem commShift_of_precomp
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    [HasShift X ℤ] [HasShift Y ℤ] [HasShift Z ℤ]
    (L : X ⥤ Y) [L.CommShift ℤ]
    [((Functor.whiskeringLeft X Y Z).obj L).Faithful]
    {F G : Y ⥤ Z} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (Functor.whiskerLeft L τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro k
  apply ((Functor.whiskeringLeft X Y Z).obj L).map_injective
  ext K
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) k K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  erw [← τ.naturality_assoc ((L.commShiftIso k).hom.app K)] at h
  exact (cancel_epi (F.map ((L.commShiftIso k).hom.app K))).1 h

/-- An exact derived adjunction commutes with shifts when its normalized complex unit does.
Source: Stacks Project, Derived Categories, Tags 05RU and 015F.
(blueprint: lem-weil-pbc-scalar-localization-unit-shift).

Proof: compose the unit precomposed with Q with the exact-derived factorization
isomorphisms. Its components are Q applied to the complex unit, so its shift
compatibility follows from that of the complex unit and Q. Cancel the factorization
isomorphisms, which commute with shifts. Faithful precomposition by the localization
Q then gives shift compatibility of the derived unit. The adjunction triangle
identities give compatibility of the counit. -/
theorem scalarLocalization_unit_commShift
    {B B' : Type*} [Category B] [Category B'] [Abelian B] [Abelian B']
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} B']
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : B' ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E.mapDerivedCategory ⊣ U.mapDerivedCategory)
    (η : ∀ K : CochainComplex B ℤ, K ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ)).obj K)
    (hη : ∀ K, adj.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map (η K))
    (hshift : ∀ (K : CochainComplex B ℤ) (k : ℤ), η (K⟦k⟧) ≫
      ((E.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ)).commShiftIso k
        ).hom.app K = (η K)⟦k⟧') : adj.CommShift ℤ := by
  let δ : DerivedCategory.Q ⋙ (E.mapDerivedCategory ⋙ U.mapDerivedCategory) ≅
      (E.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.mapDerivedCategoryFactors U.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ)) U.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  let ν := DerivedCategory.Q.rightUnitor.inv ≫
    Functor.whiskerLeft DerivedCategory.Q adj.unit ≫ δ.hom
  have hν (K : CochainComplex B ℤ) : ν.app K = DerivedCategory.Q.map (η K) := by
    simpa [ν, δ, Category.assoc] using hη K
  have : NatTrans.CommShift ν ℤ := by
    constructor
    intro k
    ext K
    change (DerivedCategory.Q.commShiftIso k).hom.app K ≫ (ν.app K)⟦k⟧' =
      ν.app (K⟦k⟧) ≫ _
    rw [hν, hν, Functor.commShiftIso_comp_hom_app, ← Category.assoc,
      ← Functor.map_comp, hshift]
    exact (DerivedCategory.Q.commShiftIso_hom_naturality (η K) k).symm
  have he : Functor.whiskerLeft DerivedCategory.Q adj.unit =
      DerivedCategory.Q.rightUnitor.hom ≫ ν ≫ δ.inv := by
    simp [ν, Category.assoc]
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q adj.unit) ℤ := by
    rw [he]
    dsimp [δ]
    infer_instance
  have := Localization.faithful_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) (DerivedCategory B)
  exact Adjunction.CommShift.mk' adj ℤ (commShift_of_precomp DerivedCategory.Q adj.unit)

end CategoryTheory
