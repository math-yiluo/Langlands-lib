/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionCochainMonoidalConstraints
import WeilConjectures.AlgebraicGeometry.SectionOrdinaryMonoidalConstraints
import WeilConjectures.AlgebraicGeometry.SectionRepresentativeTensorArrow

/-! # The regular-unit constraints of the section localization tensor map

Source: Stacks Project, Tags 06YU and 07A4; localization of the ordinary
regular-module constraints under the fixed section equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints

universe uC uA uD vC vA vD
section Descent
variable {C : Type uC} {A : Type uA} {D : Type uD}
  [Category.{vC} C] [Category.{vA} A] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory A] [MonoidalCategory D]
  (F : C ⥤ A) [F.OplaxMonoidal] [F.EssSurj]
  (U : C ⥤ D) [U.LaxMonoidal] (L : A ⥤ D) (κ : U ≅ F ⋙ L)
  (s : ∀ P Q : A, L.obj P ⊗ L.obj Q ⟶ L.obj (P ⊗ Q))
  (e : 𝟙_ D ≅ L.obj (𝟙_ A))
  (he : e.hom = Functor.LaxMonoidal.ε U ≫ κ.hom.app (𝟙_ C) ≫
    L.map (Functor.OplaxMonoidal.η F))
  (hn : ∀ {P P' Q Q' : A} (a : P ⟶ P') (b : Q ⟶ Q'),
    (L.map a ⊗ₘ L.map b) ≫ s P' Q' = s P Q ≫ L.map (a ⊗ₘ b))
  (hs : ∀ P Q : C, (κ.hom.app P ⊗ₘ κ.hom.app Q) ≫ s (F.obj P) (F.obj Q) =
    Functor.LaxMonoidal.μ U P Q ≫ κ.hom.app (P ⊗ Q) ≫
      L.map (Functor.OplaxMonoidal.δ F P Q))

include F U κ he hn hs in
private theorem descend_units (M : A) :
    (s (𝟙_ A) M ≫ L.map (λ_ M).hom = e.inv ▷ L.obj M ≫ (λ_ _).hom) ∧
    (s M (𝟙_ A) ≫ L.map (ρ_ M).hom = L.obj M ◁ e.inv ≫ (ρ_ _).hom) := by
  have hl (P : C) :
      (e.hom ▷ L.obj (F.obj P)) ≫ s (𝟙_ A) (F.obj P) ≫
        L.map (λ_ (F.obj P)).hom = (λ_ _).hom := by
    apply (cancel_epi (𝟙_ D ◁ κ.hom.app P)).mp
    calc
      _ = (Functor.LaxMonoidal.ε U ▷ U.obj P) ≫
          (κ.hom.app (𝟙_ C) ⊗ₘ κ.hom.app P) ≫
          (L.map (Functor.OplaxMonoidal.η F) ▷ L.obj (F.obj P)) ≫
          s (𝟙_ A) (F.obj P) ≫ L.map (λ_ (F.obj P)).hom := by
        rw [he]
        simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp]
      _ = (Functor.LaxMonoidal.ε U ▷ U.obj P) ≫
          Functor.LaxMonoidal.μ U (𝟙_ C) P ≫ κ.hom.app ((𝟙_ C) ⊗ P) ≫
          L.map (F.map (λ_ P).hom) := by
        have h := hn (Functor.OplaxMonoidal.η F) (𝟙 (F.obj P))
        rw [L.map_id] at h
        simp only [tensorHom_id] at h
        rw [reassoc_of% h, reassoc_of% (hs (𝟙_ C) P)]
        simp only [← L.map_comp,
          Functor.OplaxMonoidal.left_unitality_hom]
      _ = _ := by
        have hk := κ.hom.naturality (λ_ P).hom
        change U.map (λ_ P).hom ≫ κ.hom.app P =
          κ.hom.app ((𝟙_ C) ⊗ P) ≫ L.map (F.map (λ_ P).hom) at hk
        rw [← hk]
        simp only [leftUnitor_naturality]
        simpa only [Category.assoc, Functor.comp_map] using
          congrArg (fun a ↦ a ≫ κ.hom.app P)
            (Functor.LaxMonoidal.left_unitality U P).symm
  have hr (P : C) :
      (L.obj (F.obj P) ◁ e.hom) ≫ s (F.obj P) (𝟙_ A) ≫
        L.map (ρ_ (F.obj P)).hom = (ρ_ _).hom := by
    apply (cancel_epi (κ.hom.app P ▷ 𝟙_ D)).mp
    calc
      _ = (U.obj P ◁ Functor.LaxMonoidal.ε U) ≫
          (κ.hom.app P ⊗ₘ κ.hom.app (𝟙_ C)) ≫
          (L.obj (F.obj P) ◁ L.map (Functor.OplaxMonoidal.η F)) ≫
          s (F.obj P) (𝟙_ A) ≫ L.map (ρ_ (F.obj P)).hom := by
        rw [he]
        simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp]
      _ = (U.obj P ◁ Functor.LaxMonoidal.ε U) ≫
          Functor.LaxMonoidal.μ U P (𝟙_ C) ≫ κ.hom.app (P ⊗ (𝟙_ C)) ≫
          L.map (F.map (ρ_ P).hom) := by
        have h := hn (𝟙 (F.obj P)) (Functor.OplaxMonoidal.η F)
        rw [L.map_id] at h
        simp only [id_tensorHom] at h
        rw [reassoc_of% h, reassoc_of% (hs P (𝟙_ C))]
        simp only [← L.map_comp,
          Functor.OplaxMonoidal.right_unitality_hom]
      _ = _ := by
        have hk := κ.hom.naturality (ρ_ P).hom
        change U.map (ρ_ P).hom ≫ κ.hom.app P =
          κ.hom.app (P ⊗ (𝟙_ C)) ≫ L.map (F.map (ρ_ P).hom) at hk
        rw [← hk]
        simp only [rightUnitor_naturality]
        simpa only [Category.assoc, Functor.comp_map] using
          congrArg (fun a ↦ a ≫ κ.hom.app P)
            (Functor.LaxMonoidal.right_unitality U P).symm
  let P := F.objPreimage M
  let i := F.objObjPreimageIso M
  have hlM : (e.hom ▷ L.obj M) ≫ s (𝟙_ A) M ≫ L.map (λ_ M).hom =
      (λ_ _).hom := by
    apply (cancel_epi (𝟙_ D ◁ L.map i.hom)).mp
    rw [whisker_exchange_assoc]
    have h := hn (𝟙 (𝟙_ A)) i.hom
    rw [L.map_id] at h
    simp only [id_tensorHom] at h
    rw [reassoc_of% h]
    simp only [← L.map_comp, leftUnitor_naturality]
    rw [L.map_comp, reassoc_of% (hl P)]
  have hrM : (L.obj M ◁ e.hom) ≫ s M (𝟙_ A) ≫ L.map (ρ_ M).hom =
      (ρ_ _).hom := by
    apply (cancel_epi (L.map i.hom ▷ 𝟙_ D)).mp
    rw [← whisker_exchange_assoc]
    have h := hn i.hom (𝟙 (𝟙_ A))
    rw [L.map_id] at h
    simp only [tensorHom_id] at h
    rw [reassoc_of% h]
    simp only [← L.map_comp, rightUnitor_naturality]
    rw [L.map_comp, reassoc_of% (hr P)]
  constructor
  · apply (cancel_epi (e.hom ▷ L.obj M)).mp
    simpa only [Category.assoc, hom_inv_whiskerRight_assoc] using hlM
  · apply (cancel_epi (L.obj M ◁ e.hom)).mp
    simpa only [Category.assoc, whiskerLeft_hom_inv_assoc] using hrM
end Descent

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] tensorComparison qTensor totalComparison
  ordinaryTensorComparison ordinaryUnitComparison
  Mod.monoidalCategoryStruct Mod.inducingFunctorData SheafOfModules.monoidalCategory
  InternalAbelianSheafModule.sectionModuleEquivalence

section ComparisonStructure
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]

@[instance_reducible] private def oplaxOfComparisons (E : C ⥤ D) (e : E.obj (𝟙_ C) ≅ 𝟙_ D)
    (d : ∀ X Y, E.obj (X ⊗ Y) ≅ E.obj X ⊗ E.obj Y)
    (hn : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
      E.map (f ⊗ₘ g) ≫ (d X' Y').hom = (d X Y).hom ≫ (E.map f ⊗ₘ E.map g))
    (ha : ∀ X Y Z, (d (X ⊗ Y) Z).hom ≫ (d X Y).hom ▷ E.obj Z ≫
      (α_ _ _ _).hom = E.map (α_ X Y Z).hom ≫ (d X (Y ⊗ Z)).hom ≫
        E.obj X ◁ (d Y Z).hom)
    (hl : ∀ X, (d (𝟙_ C) X).hom ≫ e.hom ▷ E.obj X ≫ (λ_ _).hom =
      E.map (λ_ X).hom)
    (hr : ∀ X, (d X (𝟙_ C)).hom ≫ E.obj X ◁ e.hom ≫ (ρ_ _).hom =
      E.map (ρ_ X).hom) : E.OplaxMonoidal where
  η := e.hom
  δ X Y := (d X Y).hom
  δ_natural_left f W := by
    simpa only [E.map_id, tensorHom_id] using (hn f (𝟙 W)).symm
  δ_natural_right W f := by
    simpa only [E.map_id, id_tensorHom] using (hn (𝟙 W) f).symm
  oplax_associativity := ha
  oplax_left_unitality X := by
    apply (cancel_mono (λ_ (E.obj X)).hom).mp
    have h := (congrArg (fun a ↦ E.map (λ_ X).inv ≫ a) (hl X)).symm
    simpa only [Category.assoc, ← E.map_comp, Iso.inv_hom_id, E.map_id,
      Category.id_comp] using h
  oplax_right_unitality X := by
    apply (cancel_mono (ρ_ (E.obj X)).hom).mp
    have h := (congrArg (fun a ↦ E.map (ρ_ X).inv ≫ a) (hr X)).symm
    simpa only [Category.assoc, ← E.map_comp, Iso.inv_hom_id, E.map_id,
      Category.id_comp] using h

@[instance_reducible] private def monoidalOfComparisons (E : C ⥤ D)
    (o : E.OplaxMonoidal) (e : E.obj (𝟙_ C) ≅ 𝟙_ D)
    (d : ∀ X Y, E.obj (X ⊗ Y) ≅ E.obj X ⊗ E.obj Y)
    (he : o.η = e.hom) (hd : ∀ X Y, o.δ X Y = (d X Y).hom) : E.Monoidal := by
  let := o
  exact (Functor.CoreMonoidal.mk' e.symm (fun X Y ↦ (d X Y).symm)
    (by
      intro X Y f Z
      dsimp only [Iso.symm_inv]
      rw [← hd X Z, ← hd Y Z]
      exact o.δ_natural_left f Z)
    (by
      intro X Y Z f
      dsimp only [Iso.symm_inv]
      rw [← hd Z X, ← hd Z Y]
      exact o.δ_natural_right Z f)
    (by
      intro X Y Z
      dsimp only [Iso.symm_inv]
      rw [← hd, ← hd, ← hd, ← hd]
      exact o.oplax_associativity X Y Z)
    (by
      intro X
      dsimp only [Iso.symm_inv]
      rw [← hd, ← he]
      exact o.oplax_left_unitality X)
    (by
      intro X
      dsimp only [Iso.symm_inv]
      rw [← hd, ← he]
      exact o.oplax_right_unitality X)).toMonoidal
omit [MonoidalCategory D] in
private theorem transportTensorMap (E : C ≌ D) {X X' Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := TensorFunctorTransport.monoidal E
    (TensorFunctorTransport.tensorFunctor E).map (Prod.mkHom f g) = f ⊗ₘ g := rfl
end ComparisonStructure

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem internalLocalizationUnit (T : Scheme.{u}) :
    Functor.LaxMonoidal.ε (DerivedCategory.Q (C := internalModules Λ T)) = 𝟙 _ := by
  change (𝟙 _ ≫ (DerivedCategory.Qh (C := internalModules Λ T)).map
    (𝟙 ((HomotopyCategory.quotient (internalModules Λ T) (.up ℤ)).obj
      (𝟙_ (CochainComplex (internalModules Λ T) ℤ))))) ≫
    (DerivedCategory.quotientCompQhIso (internalModules Λ T)).hom.app
      (𝟙_ (CochainComplex (internalModules Λ T) ℤ)) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    CategoryTheory.Quotient.lift.isLift_hom]
  rfl

/-- The fixed localization tensorator has the specified regular-unit constraints.
Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 07A4; the source and
target normalized modelTensor unitor equations in Steps 2–3 of
lem-pd-section-resolving-oplax-unit-models.

Proof: on termwise images of internal complexes, substitute the defining
representative normalization for qTensor. Its binary comparison is the inverse
of tensorComparison followed by the internal lax localization tensorator, the
section localization factor, and the localized ordinary total comparison. Apply
naturality to the ordinary unit comparison. The ordinary total comparison
preserves both unitors: check the total comparison equation degreewise on
direct-sum summands. Only the degree-zero term of the unit survives, and its
equation is the ordinary left or right unit law of the section equivalence.
The internal lax localization satisfies its left and right unit laws, with
identity unit comparison. The fixed section localization and ordinary unit comparisons
compose to regular, so cancelling their inverse factors gives the two displayed
equalities. Every section complex is isomorphic to a termwise image under the
section equivalence. Naturality of qTensor and of both unitors transports these
equalities along that isomorphism to the given complex. This uses no pullback
functor, no resolving hypothesis, and no derived pullback constraint.
(auxiliary; not a blueprint node). -/
theorem section_localization_unit_constraints (T : Scheme.{u})
    (P : CochainComplex (modules Λ T) ℤ) :
    letI := derivedMonoidal Λ T
    (modelTensor Λ T (𝟙_ (CochainComplex (modules Λ T) ℤ)) P ≫
        DerivedCategory.Q.map (λ_ P).hom =
      regularLeft DerivedCategory.Q (cast (by rfl) (regular Λ T)) (DerivedCategory.Q.obj P)) ∧
    (modelTensor Λ T P (𝟙_ (CochainComplex (modules Λ T) ℤ)) ≫
        DerivedCategory.Q.map (ρ_ P).hom =
      regularRight DerivedCategory.Q (cast (by rfl) (regular Λ T)) (DerivedCategory.Q.obj P)) := by
  let := derivedMonoidal Λ T
  let F := (equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)
  let : F.IsEquivalence :=
    ((equivalence Λ T).mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  let G := (derivedEquivalence Λ T).functor
  obtain ⟨ha, hl, hr⟩ := section_ordinary_monoidal_constraints Λ T
  let E := (equivalence Λ T).functor
  let o := oplaxOfComparisons E (ordinaryUnitComparison Λ T) (ordinaryTensorComparison Λ T)
    (fun f g ↦ sectionOrdinaryTensorNaturality Λ T _ _ _ _ f g) ha hl hr
  let m := monoidalOfComparisons E o (ordinaryUnitComparison Λ T)
    (ordinaryTensorComparison Λ T) rfl (fun _ _ ↦ rfl)
  let := m
  have hηo : Functor.OplaxMonoidal.η E = (ordinaryUnitComparison Λ T).hom := rfl
  have hδo (M N : internalModules Λ T) :
      Functor.OplaxMonoidal.δ E M N = (ordinaryTensorComparison Λ T M N).hom := rfl
  obtain ⟨hd, hu⟩ := section_cochain_monoidal_constraints Λ T hδo hηo
  obtain ⟨e₀, he₀, o, hη, hδ⟩ :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 2, u + 1}
      Λ T).2.2.2.2.2.2.2.2
  have hcon : ∃ o' : G.OplaxMonoidal,
      o'.η = 𝟙 _ ∧ ∀ M N, o'.δ M N = (tensorComparison Λ T).hom.app (M, N) := by
    simpa only [KFlatSectionComparison.ConstraintCondition, G, derivedMonoidal,
      transportedDerivedMonoidal,
      TensorFunctorTransport.monoidal_eq] using
      (show KFlatSectionComparison.ConstraintCondition Λ T from ⟨o, hη, hδ⟩)
  obtain ⟨o', hη', hδ'⟩ := hcon
  let : G.Monoidal := monoidalOfComparisons G o' (Iso.refl _)
    (fun M N ↦ (tensorComparison Λ T).app (M, N)) hη' hδ'
  have hμ (M N : DerivedCategory (internalModules Λ T)) :
      Functor.LaxMonoidal.μ G M N = (tensorComparison Λ T).inv.app (M, N) := by
    rfl
  have hε : Functor.LaxMonoidal.ε G = 𝟙 _ := by rfl
  let U := (DerivedCategory.Q (C := internalModules Λ T)) ⋙ G
  have hεU : Functor.LaxMonoidal.ε U = 𝟙 _ := by
    change Functor.LaxMonoidal.ε G ≫
      G.map (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := internalModules Λ T))) = _
    rw [hε]
    rw [internalLocalizationUnit]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  apply descend_units F U DerivedCategory.Q (sectionLocalizationIso Λ T)
    (modelTensor Λ T) (regular Λ T) ?_ ?_ ?_ P
  · change (sectionLocalizationComparison Λ T (𝟙_ _)).hom ≫
        DerivedCategory.Q.map (totalUnitComparison Λ T).hom = _
    simp only [F, hεU, hu, Category.id_comp]
    rfl
  · intro A A' B B' a b
    simpa only [qTensorArrow, modelTensor, tensor, transportTensorMap] using
      qTensorArrow_naturality Λ T a b
  · intro A B
    apply (cancel_epi ((tensorComparison Λ T).hom.app
      (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B))).mp
    have h := qTensorArrow_normalization Λ T A B
    simp only [U, Functor.LaxMonoidal.comp_μ, hμ]
    simp only [F, hd, Category.assoc, Iso.hom_inv_id_app_assoc]
    simpa only [modelTensor, qTensorArrow, tensor, transportTensorMap, G,
      derivedSectionFunctor, derivedFunctor, derivedEquivalence, Functor.asEquivalence,
      internalLocalizationFunctor, internalQTensorArrow, cochainLocalizationIso,
      derivedSectionTensorIso, sectionLocalizationIso, sectionLocalizationComparison,
      cochainSectionEquivalence, retainedCochainFunctor_eq, Iso.app_hom,
      cochainTensorComparison] using h.symm

end AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints
