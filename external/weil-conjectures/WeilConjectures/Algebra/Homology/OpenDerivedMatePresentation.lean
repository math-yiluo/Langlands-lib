/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Presentation of derived open-extension mates on complexes

Source: Stacks Project, Tags 08BT and 08BW.
-/

@[expose] public section

universe w vA vB vC uA uB uC

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Adjunction

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  {L : B ⥤ A} {R : A ⥤ B} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- Localize the termwise adjunction of exact functors. 
(blueprint: lem-sc-localization-nested-adjunction-mate)
-/
def onDerivedCategory (adj : L ⊣ R) : L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  letI : CatCommSq (L.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

/-- Compare a chosen left adjoint with the termwise model on a representative complex. 
(blueprint: lem-sc-localization-nested-adjunction-mate)
-/
def derivedPresentation (adj : L ⊣ R)
    {LD : DerivedCategory B ⥤ DerivedCategory A} (d : LD ⊣ R.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E) :
    LD.obj (R.mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  (d.leftAdjointUniq adj.onDerivedCategory).app _ ≪≫
    L.mapDerivedCategory.mapIso
      (R.mapDerivedCategory.mapIso e.symm ≪≫ R.mapDerivedCategoryFactors.app K) ≪≫
    L.mapDerivedCategoryFactors.app _

/-- The presentation carries the chosen counit to the termwise counit. 
(blueprint: lem-sc-localization-nested-adjunction-mate)
-/
theorem derivedPresentation_counit (adj : L ⊣ R)
    {LD : DerivedCategory B ⥤ DerivedCategory A} (d : LD ⊣ R.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E) :
    (adj.derivedPresentation d K e).hom ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K) ≫
        e.hom = d.counit.app E := by
  have hc : adj.onDerivedCategory.counit.app (DerivedCategory.Q.obj K) =
      L.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K) := by
    simp only [onDerivedCategory, localization_counit_app]
    rfl
  dsimp only [derivedPresentation, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  have hn := adj.onDerivedCategory.counit.naturality e.inv
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← reassoc_of% hc, reassoc_of% hn]
  simp

/-- The transpose of the presentation is the localized termwise unit. -/
private theorem derivedPresentation_unit (adj : L ⊣ R)
    {LD : DerivedCategory B ⥤ DerivedCategory A} (d : LD ⊣ R.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E) :
    d.unit.app (R.mapDerivedCategory.obj E) ≫
        R.mapDerivedCategory.map (adj.derivedPresentation d K e).hom =
      R.mapDerivedCategory.map e.inv ≫ R.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        R.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  have hu : adj.onDerivedCategory.unit.app
      (DerivedCategory.Q.obj ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        R.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    simp only [onDerivedCategory, localization_unit_app]
    rfl
  dsimp only [derivedPresentation, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Category.assoc, unit_leftAdjointUniq_hom_app d adj.onDerivedCategory]
  simp only [Category.assoc]
  have hn := adj.onDerivedCategory.unit.naturality
    (R.mapDerivedCategory.map e.inv ≫ R.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Functor.map_comp, Category.assoc] at hn
  rw [← reassoc_of% hn]
  rw [hu]
  simp [← Functor.map_comp, Category.assoc]

/-- The derived restriction comparison agrees with its termwise model under Q. -/
private theorem derivedComparison_fac
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
    {R2 : A ⥤ C} {T : B ⥤ C} [R2.Additive] [T.Additive]
    [PreservesFiniteLimits R2] [PreservesFiniteColimits R2]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (c : R ⋙ T ≅ R2) (K : CochainComplex A ℤ) :
    letI : PreservesFiniteLimits (R ⋙ T) := comp_preservesFiniteLimits R T
    letI : PreservesFiniteColimits (R ⋙ T) := comp_preservesFiniteColimits R T
    let cD := Functor.mapDerivedCategoryCompIso R T ≪≫
      Functor.mapDerivedCategoryNatIso c
    cD.hom.app (DerivedCategory.Q.obj K) ≫ R2.mapDerivedCategoryFactors.hom.app K =
      T.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        T.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).hom.app K) := by
  let : PreservesFiniteLimits (R ⋙ T) := comp_preservesFiniteLimits R T
  let : PreservesFiniteColimits (R ⋙ T) := comp_preservesFiniteColimits R T
  dsimp only
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ T))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
    ext n
    rfl
  have hc := Functor.mapDerivedCategoryCompIso_fac R T K
  erw [hi, Functor.map_id, Category.comp_id] at hc
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

/-- Exact localization carries a nested adjunction mate to its derived mate.

Source: Stacks Project, Tags 08BT and 08BW; compatibility with localization of the
unit and counit (Mathlib `Adjunction.localization_unit_app` and
`Adjunction.localization_counit_app`).
(blueprint: lem-sc-localization-nested-adjunction-mate).

Proof: Use the adjunction induced termwise on complexes, whose unit and counit in
each degree are those of the original adjunction. The degreewise hypothesis is
therefore equality of complex morphisms, by extensionality. Localize that equality.
Expand the localized unit and counit on Q K using the localization formulas. The
factorization isomorphisms for composition and for the comparison c identify the
localized comparison with cD. Cancel inverse factorization isomorphisms to obtain
the assertion for the localized adjunctions and E = Q K. Naturality transports this
identity along e. Finally the unique isomorphisms from the chosen derived left
adjoints to the localized ones carry their units and counits to each other; the
unit and counit identities for `leftAdjointUniq` give the displayed formula for
arbitrary d1 and d2. This is an equality for a single nested restriction: no cover,
short exact sequence, or distinguished triangle is assumed or asserted. -/
theorem derivedPresentation_mate
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
    {L2 : C ⥤ A} {R2 : A ⥤ C} {T : B ⥤ C}
    [L2.Additive] [R2.Additive] [T.Additive]
    [PreservesFiniteLimits L2] [PreservesFiniteColimits L2]
    [PreservesFiniteLimits R2] [PreservesFiniteColimits R2]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a1 : L ⊣ R) (a2 : L2 ⊣ R2) (c : R ⋙ T ≅ R2)
    {LD1 : DerivedCategory B ⥤ DerivedCategory A}
    {LD2 : DerivedCategory C ⥤ DerivedCategory A}
    (d1 : LD1 ⊣ R.mapDerivedCategory) (d2 : LD2 ⊣ R2.mapDerivedCategory)
    (K : CochainComplex A ℤ) {E : DerivedCategory A} (e : DerivedCategory.Q.obj K ≅ E)
    (f : (L2.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((R2.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hf : ∀ n, f.f n = (a2.homEquiv _ _).symm
      (c.inv.app (K.X n) ≫ T.map (a1.unit.app (R.obj (K.X n))) ≫
        c.hom.app (L.obj (R.obj (K.X n))))) :
    letI : PreservesFiniteLimits (R ⋙ T) := comp_preservesFiniteLimits R T
    letI : PreservesFiniteColimits (R ⋙ T) := comp_preservesFiniteColimits R T
    let cD := Functor.mapDerivedCategoryCompIso R T ≪≫
      Functor.mapDerivedCategoryNatIso c
    let κ := (d2.homEquiv _ _).symm
      (cD.inv.app E ≫ T.mapDerivedCategory.map
        (d1.unit.app (R.mapDerivedCategory.obj E)) ≫
        cD.hom.app (LD1.obj (R.mapDerivedCategory.obj E)))
    (a2.derivedPresentation d2 K e).hom ≫ DerivedCategory.Q.map f =
      κ ≫ (a1.derivedPresentation d1 K e).hom := by
  let : PreservesFiniteLimits (R ⋙ T) := comp_preservesFiniteLimits R T
  let : PreservesFiniteColimits (R ⋙ T) := comp_preservesFiniteColimits R T
  let cD := Functor.mapDerivedCategoryCompIso R T ≪≫
    Functor.mapDerivedCategoryNatIso c
  let cK := Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)
  -- Identify the transpose of f degreewise, before localizing.
  have hK : (a2.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
      ((R2.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (R2.mapHomologicalComplex (ComplexShape.up ℤ)).map f =
      cK.inv.app K ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((a1.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        cK.hom.app ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    ext n
    change a2.unit.app (R2.obj (K.X n)) ≫ R2.map (f.f n) =
      c.inv.app (K.X n) ≫ T.map (a1.unit.app (R.obj (K.X n))) ≫
        c.hom.app (L.obj (R.obj (K.X n)))
    rw [hf]
    exact (a2.homEquiv _ _).apply_symm_apply _
  change (a2.derivedPresentation d2 K e).hom ≫ DerivedCategory.Q.map f =
    (d2.homEquiv _ _).symm
      (cD.inv.app E ≫ T.mapDerivedCategory.map
        (d1.unit.app (R.mapDerivedCategory.obj E)) ≫
        cD.hom.app (LD1.obj (R.mapDerivedCategory.obj E))) ≫
      (a1.derivedPresentation d1 K e).hom
  -- The adjunction detects equality; transport both transposes to complexes.
  apply (d2.homEquiv _ _).injective
  simp only [homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [homEquiv_unit]
  simp only [← Category.assoc]
  rw [derivedPresentation_unit a2 d2 K e]
  simp only [Category.assoc]
  have hnR := R2.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hnR
  rw [← hnR, ← DerivedCategory.Q.map_comp_assoc, hK]
  have hnC := cD.hom.naturality (a1.derivedPresentation d1 K e).hom
  dsimp only [Functor.comp_map] at hnC
  rw [← hnC, ← T.mapDerivedCategory.map_comp_assoc,
    derivedPresentation_unit a1 d1 K e]
  simp only [Functor.map_comp, Category.assoc]
  -- Cancel the final factorization and use naturality to align the two composites.
  let M := (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  apply (cancel_mono (R2.mapDerivedCategoryFactors.hom.app M)).1
  dsimp only [M]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  rw [derivedComparison_fac c M]
  dsimp only [M]
  simp only [← T.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  have hnT := T.mapDerivedCategoryFactors.hom.naturality
    ((a1.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  dsimp only [Functor.comp_map] at hnT
  rw [reassoc_of% hnT]
  have hnE := cD.inv.naturality e.inv
  dsimp only [Functor.comp_map] at hnE
  rw [← reassoc_of% hnE]
  -- The inverse comparison formula follows by cancelling Q(cK.hom).
  have hci : cD.inv.app (DerivedCategory.Q.obj K) ≫
      T.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        T.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      R2.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (cK.inv.app K) := by
    apply (cancel_mono (DerivedCategory.Q.map (cK.hom.app K))).1
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    simp only [Functor.map_id, Category.comp_id]
    rw [← derivedComparison_fac c K]
    change cD.inv.app (DerivedCategory.Q.obj K) ≫
      cD.hom.app (DerivedCategory.Q.obj K) ≫
        R2.mapDerivedCategoryFactors.hom.app K = R2.mapDerivedCategoryFactors.hom.app K
    simp
  rw [reassoc_of% hci]

end CategoryTheory.Adjunction

end
