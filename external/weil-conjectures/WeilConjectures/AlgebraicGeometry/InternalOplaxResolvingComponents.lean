/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.SectionKFlatTensorComparison
public import WeilConjectures.AlgebraicGeometry.SectionTotalOplaxComparisonData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.Topology.ProfiniteCondensedRing
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # Actual internal oplax components on resolving models

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 07A2 and 07A4
(auxiliary; not a blueprint node).

The generic predicates expose the component equations of the specified localized arrows.
The final statement specializes them to the actual internal pro-etale module pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- A natural square commutes also on the actual inverse images of specified arrows.
The isomorphisms have the functor images as their forward maps, fixing the inverses.
Source: Stacks 07A4, resolving localization
(auxiliary; not a blueprint node). -/
def ResolvingInverseSquares {A : Type a} [Category.{b} A]
    {B : Type c} [Category.{d} B] {U V : A ⥤ B}
    (τ : U ⟶ V) (W : MorphismProperty A) : Prop :=
  ∀ (P Q : A) (s : P ⟶ Q), W s →
    ∃ (i : U.obj P ≅ U.obj Q) (j : V.obj P ≅ V.obj Q),
      i.hom = U.map s ∧ j.hom = V.map s ∧
        i.inv ≫ τ.app P = τ.app Q ≫ j.inv

private theorem inverse_squares_of_maps {A : Type a} [Category.{b} A]
    {B : Type c} [Category.{d} B] {U V : A ⥤ B}
    (τ : U ⟶ V) (W : MorphismProperty A)
    (hU : ∀ (P Q : A) (s : P ⟶ Q), W s → IsIso (U.map s))
    (hV : ∀ (P Q : A) (s : P ⟶ Q), W s → IsIso (V.map s)) :
    ResolvingInverseSquares τ W := by
  intro P Q s hs
  have := hU P Q s hs
  have := hV P Q s hs
  refine ⟨asIso (U.map s), asIso (V.map s), rfl, rfl, ?_⟩
  apply (cancel_epi (U.map s)).1
  simp only [asIso_inv, IsIso.hom_inv_id_assoc]
  rw [τ.naturality_assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem isIso_map_of_components {A : Type a} [Category.{b} A]
    {B : Type c} [Category.{d} B] {U V : A ⥤ B}
    (τ : U ⟶ V) {P Q : A} (s : P ⟶ Q)
    [IsIso (τ.app P)] [IsIso (τ.app Q)] [IsIso (U.map s)] : IsIso (V.map s) := by
  have h : V.map s = CategoryTheory.inv (τ.app P) ≫ U.map s ≫ τ.app Q := by
    rw [τ.naturality, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

section Components
variable {C : Type a} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type c} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal]

/-- The actual comparison a: L(r⁻¹) followed by the resolution transformation.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def resolvingComparisonA := Functor.uncurry.map F.leftDerivedDerivedTensorCounit

/-- The actual comparison c: tensor the resolution transformations, then apply r⁻¹.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def resolvingComparisonC := Functor.uncurry.map F.derivedTensorLeftDerivedCounit

/-- The homotopy total oplax arrow, followed by the derived localization.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def resolvingTotalArrow :=
  Functor.uncurry.map (Functor.postcompose₂MapWhiskeringLeft₂
    (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F) DerivedCategory.Qh)

/-- Restrict the specified localized tensor transformation to homotopy representatives.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def resolvingDelta (δ : F.leftDerivedDerivedTensor ⟶ F.derivedTensorLeftDerived) :=
  Functor.uncurry.map
    ((((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map δ)

/-- Quasi-isomorphisms between resolving pairs, in both homotopy variables.
Source: Stacks 0G7E and 07A4 (auxiliary; not a blueprint node). -/
def resolvingPairArrows (P : ObjectProperty (CochainComplex C ℤ)) :
    MorphismProperty (HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ)) :=
  fun A B s ↦ P A.1.as ∧ P A.2.as ∧ P B.1.as ∧ P B.2.as ∧
    HomotopyCategory.quasiIso C (.up ℤ) s.1 ∧
    HomotopyCategory.quasiIso C (.up ℤ) s.2

/-- The resolving component assertion for a fixed localized tensor transformation.
Its comparison transformations are the existing derived counits; no new lift is chosen.
Source: Stacks 0G7E and 07A4 (auxiliary; not a blueprint node). -/
def ResolvingOplaxComponents
    (P : ObjectProperty (CochainComplex C ℤ))
    (Q : ObjectProperty (CochainComplex D ℤ))
    (δ : F.leftDerivedDerivedTensor ⟶ F.derivedTensorLeftDerived) : Prop :=
  (∀ A : HomotopyCategory C (.up ℤ), P A.as →
    Q ((F.mapHomotopyCategory (.up ℤ)).obj A).as ∧
      IsIso (F.leftDerivedFunctorCounit.app A)) ∧
  (∀ A B : HomotopyCategory C (.up ℤ), P A.as → P B.as →
    IsIso (F.leftDerivedFunctorCounit.app (A ⊗ B)) ∧
    IsIso ((resolvingComparisonA F).app (A, B)) ∧
    IsIso ((resolvingComparisonC F).app (A, B)) ∧
    (resolvingDelta F δ).app (A, B) ≫ (resolvingComparisonC F).app (A, B) =
      (resolvingComparisonA F).app (A, B) ≫ (resolvingTotalArrow F).app (A, B)) ∧
  ResolvingInverseSquares (resolvingComparisonA F) (resolvingPairArrows P) ∧
  ResolvingInverseSquares (resolvingComparisonC F) (resolvingPairArrows P) ∧
  ResolvingInverseSquares (resolvingTotalArrow F) (resolvingPairArrows P) ∧
  ResolvingInverseSquares (resolvingDelta F δ) (resolvingPairArrows P)

attribute [local irreducible] DerivedCategory.Qh CategoryTheory.Functor.mapHomotopyCategory
  DerivedCategory.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.leftDerivedTensorComparison
  CategoryTheory.Functor.leftDerivedDerivedTensorCounit
  CategoryTheory.Functor.derivedTensorLeftDerivedCounit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem kFlat_of_acyclic_tensor (P : CochainComplex C ℤ)
    (hP : ∀ N : CochainComplex C ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P (curriedTensor C)).Acyclic) :
    (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor C))).2 (hP N hN)
  exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem acyclic_tensor_of_kFlat (P : CochainComplex C ℤ)
    (hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :
    ∀ N : CochainComplex C ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P (curriedTensor C)).Acyclic := by
  intro N hN
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    (((HomotopyCategory.kFlat_iff_preserves_acyclic _).1 hP) _
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)).2

private theorem components_of_kFlat
    (P : ObjectProperty (CochainComplex C ℤ))
    (Q : ObjectProperty (CochainComplex D ℤ))
    (hP : ∀ A : HomotopyCategory C (.up ℤ), P A.as →
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat A)
    (hF : ∀ A : HomotopyCategory C (.up ℤ), P A.as →
      Q ((F.mapHomotopyCategory (.up ℤ)).obj A).as ∧
      (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomotopyCategory (.up ℤ)).obj A)) :
    ResolvingOplaxComponents F P Q F.leftDerivedTensorComparison := by
  have hη (A : HomotopyCategory C (.up ℤ)) (hA : P A.as) :
      IsIso (F.leftDerivedFunctorCounit.app A) :=
    F.isIso_leftDerivedFunctorCounit_app_of_kFlat' A (hP A hA)
  have ha (A B : HomotopyCategory C (.up ℤ)) (hA : P A.as) (hB : P B.as) :
      IsIso ((resolvingComparisonA F).app (A, B)) := by
    have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' (A ⊗ B)
      ((HomotopyCategory.quasiIso C (.up ℤ)).kFlat.prop_tensor (hP A hA) (hP B hB))
    have hμ : IsIso (LaxMonoidal.μ DerivedCategory.Qh A B) :=
      isIso_μNatTrans_Qh_app_app_of_kFlat A B (hP B hB)
    change IsIso (((F.leftDerivedDerivedTensorCounit).app A).app B)
    rw [leftDerivedDerivedTensorCounit_app_app]
    infer_instance
  have hc (A B : HomotopyCategory C (.up ℤ)) (hA : P A.as) (hB : P B.as) :
      IsIso ((resolvingComparisonC F).app (A, B)) := by
    have := hη A hA
    have := hη B hB
    have hμ : IsIso (LaxMonoidal.μ DerivedCategory.Qh
        ((F.mapHomotopyCategory (.up ℤ)).obj A)
        ((F.mapHomotopyCategory (.up ℤ)).obj B)) :=
      isIso_μNatTrans_Qh_app_app_of_kFlat
        ((F.mapHomotopyCategory (.up ℤ)).obj A) _ (hF B hB).2
    change IsIso (((F.derivedTensorLeftDerivedCounit).app A).app B)
    rw [derivedTensorLeftDerivedCounit_app_app]
    infer_instance
  have hsrcA (A B : HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ))
      (s : A ⟶ B) (hs : resolvingPairArrows P s) :
      IsIso ((Functor.uncurry.obj
        ((((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
          F.leftDerivedDerivedTensor)).map s) := by
    have := Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ hs.2.2.2.2.1
    have := Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ hs.2.2.2.2.2
    dsimp [Functor.uncurry_obj_map, leftDerivedDerivedTensor]
    infer_instance
  have hsrcC (A B : HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ))
      (s : A ⟶ B) (hs : resolvingPairArrows P s) :
      IsIso ((Functor.uncurry.obj
        ((((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
          F.derivedTensorLeftDerived)).map s) := by
    have := Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ hs.2.2.2.2.1
    have := Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ hs.2.2.2.2.2
    dsimp [Functor.uncurry_obj_map, derivedTensorLeftDerived]
    infer_instance
  have htgtA (A B : HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ))
      (s : A ⟶ B) (hs : resolvingPairArrows P s) :
      IsIso ((Functor.uncurry.obj
        ((Functor.postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh)).obj (curriedTensor _))).map s) := by
    have := ha A.1 A.2 hs.1 hs.2.1
    have := ha B.1 B.2 hs.2.2.1 hs.2.2.2.1
    have := hsrcA A B s hs
    exact isIso_map_of_components (resolvingComparisonA F) s
  have htgtC (A B : HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ))
      (s : A ⟶ B) (hs : resolvingPairArrows P s) :
      IsIso ((Functor.uncurry.obj
        ((((Functor.whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
          (F.mapHomotopyCategory (.up ℤ))).obj
          ((Functor.postcompose₂.obj DerivedCategory.Qh).obj (curriedTensor _)))).map s) := by
    have := hc A.1 A.2 hs.1 hs.2.1
    have := hc B.1 B.2 hs.2.2.1 hs.2.2.2.1
    have := hsrcC A B s hs
    exact isIso_map_of_components (resolvingComparisonC F) s
  refine ⟨fun A hA ↦ ⟨(hF A hA).1, hη A hA⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B hA hB
    exact ⟨F.isIso_leftDerivedFunctorCounit_app_of_kFlat' _
        ((HomotopyCategory.quasiIso C (.up ℤ)).kFlat.prop_tensor (hP A hA) (hP B hB)),
      ha A B hA hB, hc A B hA hB,
      F.leftDerivedTensorComparison_app_app_comp_counit A B⟩
  · apply inverse_squares_of_maps (resolvingComparisonA F)
    · exact hsrcA
    · exact htgtA
  · apply inverse_squares_of_maps (resolvingComparisonC F)
    · exact hsrcC
    · exact htgtC
  · apply inverse_squares_of_maps (resolvingTotalArrow F)
    · exact htgtA
    · exact htgtC
  · apply inverse_squares_of_maps (resolvingDelta F F.leftDerivedTensorComparison)
    · exact hsrcA
    · exact hsrcC

end Components
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] internalPullMonoidal CondensedRing.monoidal_upperStar
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.leftDerivedTensorComparison

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem internal_kFlat (T : Scheme.{u})
    (A : HomotopyCategory (internalModules Λ T) (.up ℤ))
    (hA : KFlatSectionComparison.internalResolving Λ T A.as) :
    (HomotopyCategory.quasiIso (internalModules Λ T) (.up ℤ)).kFlat A := by
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  exact Functor.kFlat_of_acyclic_tensor A hA.1

private theorem internal_pull_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internalModules Λ Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) := by
  have : (Mod.extendScalars (condensedPullbackHom Λ f)).IsEquivalence := by
    have : (Mod.comap (asIso (condensedPullbackHom Λ f)).inv).IsEquivalence :=
      (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm.isEquivalence_functor
    exact Functor.isEquivalence_of_iso
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm
  exact ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (CondensedRing.upperStar Λ f))
      (.up ℤ)).app P)
    ((Mod.extendScalars (condensedPullbackHom Λ f))
      |>.kFlat_mapHomologicalComplex_obj_of_isEquivalence
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
          |>.kFlat_mapHomologicalComplex_obj P hP))

private theorem internal_pull_resolving {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : HomotopyCategory (internalModules Λ Y) (.up ℤ))
    (hA : KFlatSectionComparison.internalResolving Λ Y A.as) :
    KFlatSectionComparison.internalResolving Λ X
        (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj A).as ∧
      (HomotopyCategory.quasiIso (internalModules Λ X) (.up ℤ)).kFlat
        (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj A) := by
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  have hk := internal_pull_kFlat Λ f A
    ((HomotopyCategory.kFlat_quotient_obj_iff A).1 (internal_kFlat Λ Y _ hA))
  have hk' := (HomotopyCategory.kFlat_quotient_obj_iff _).2 hk
  have hk'' := (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
    ((CondensedRing.upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ) |>.app A).symm hk'
  refine ⟨⟨?_, ?_⟩, hk''⟩
  · exact Functor.acyclic_tensor_of_kFlat _ hk'
  · intro n
    have hf : ObjectProperty.flat (A.X n) :=
      ⟨(exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight (A.X n)).symm (hA.2 n), hA.2 n⟩
    exact (Functor.PreservesFlat.flat_obj (F := CondensedRing.upperStar Λ f) hf).2

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem internal_monoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullMonoidal Λ f = CondensedRing.monoidal_upperStar Λ f := by
  apply Functor.Monoidal.toOplaxMonoidal_injective
  unfold internalPullMonoidal
  exact internalPullOplax_eq_canonical Λ f

/-- The actual internal oplax components on flat-term K-flat models.
Source: Stacks 0G7E, 07A2 and 07A4; the component identities are agent calculations
(auxiliary; not a blueprint node).

Proof, following the six DAG steps.
1. The section K-flat comparison preserves and reflects resolving membership. Transport
   ringed pullback preservation through the ordinary operations comparison; use the
   K-flat total tensor model theorem for total closure. The regular complex resolves.
2. The independent-universe pullback computation makes the section resolution counit
   invertible. Derived pushpull normalization conjugates the image of the internal
   counit to this map. The derived equivalence reflects invertibility. Apply to the
   two factors, their signed tensor total and the regular complex.
3. The existing comparisonA is L(r inverse) followed by eta, while comparisonC is
   eta tensor eta followed by r inverse. Their factors are invertible on these models.
4. The total oplax comparison identifies b on the homotopy category. Two-variable
   localization computes its lift as c inverse followed by q(b) after a. Uniqueness
   identifies the lift with internalDelta; hence delta followed by c equals a then q(b).
5. Localizing the actual ordinary unit gives eta followed by q(u), with the identity
   target comparison. This is the specified derived unit, not a new unit choice.
6. The four maps are natural transformations. Comparisons a,c identify their functors
   with restrictions of derived functors, so resolving quasi-isomorphisms are inverted.
   Multiply the naturality squares by their inverse vertical arrows to obtain the
   four ResolvingInverseSquares assertions. Compositions cover inversion in either
   variable. There is no flatness assumption on a coefficient map or boundedness.
-/
theorem internal_oplax_resolving_components {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.ResolvingOplaxComponents (CondensedRing.upperStar Λ f)
      (KFlatSectionComparison.internalResolving Λ Y)
      (KFlatSectionComparison.internalResolving Λ X) (internalDelta Λ f) ∧
    KFlatSectionComparison.internalResolving Λ Y
      (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ∧
    (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom =
      (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))) ≫
        DerivedCategory.Qh.map
          (((CondensedRing.upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).hom.app
              (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)) ≫
            (HomotopyCategory.quotient _ (.up ℤ)).map (actualInternalTotalUnit Λ f)) := by
  constructor
  · have hδ : internalDelta Λ f =
        (CondensedRing.upperStar Λ f).leftDerivedTensorComparison := by
      unfold internalDelta
      rw [internal_monoidal_eq Λ f]
    rw [hδ]
    exact Functor.components_of_kFlat (CondensedRing.upperStar Λ f)
      _ _ (internal_kFlat Λ Y) (internal_pull_resolving Λ f)
  constructor
  · exact (KFlatSectionComparison.section_kflat_tensor_comparison.{u, 0, 0} Λ Y).2.2.2.2.2.2.2.1
  · unfold CondensedRing.leftDerivedUpperStarUnitIso actualInternalTotalUnit
    rfl

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
