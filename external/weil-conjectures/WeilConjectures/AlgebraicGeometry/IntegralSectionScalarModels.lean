/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import all WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalars
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Scalar realization under the integral section comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule

section FinitePresentationComparison
universe v w
variable {A : Type u} [CommRing A] {C : Type v} [Category.{w} C] [Abelian C]
  (F G : ModuleCat.{u + 1} A ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteColimits F] [PreservesFiniteColimits G]

private abbrev scalarRegular (A : Type u) [CommRing A] : ModuleCat.{u + 1} A :=
  ModuleCat.of A (ULift.{u + 1} A)

private def scalarBiproductIso (n : ℕ) :
    FiniteConstantModel.freeScalars A n ≅
      ⨁ (fun _ : Fin n ↦ scalarRegular A) :=
  (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ scalarRegular A)).symm

private def scalarFreeComparison (e : F.obj (scalarRegular A) ≅ G.obj (scalarRegular A))
    (n : ℕ) : F.obj (FiniteConstantModel.freeScalars A n) ≅
      G.obj (FiniteConstantModel.freeScalars A n) :=
  F.mapIso (scalarBiproductIso n) ≪≫ F.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ : Fin n ↦ e) ≪≫
    (G.mapBiproduct _).symm ≪≫ (G.mapIso (scalarBiproductIso n)).symm

omit [PreservesFiniteColimits G] in
private theorem scalarFreeComparison_natural
    (e : F.obj (scalarRegular A) ≅ G.obj (scalarRegular A))
    (he : ∀ f : scalarRegular A ⟶ scalarRegular A,
      F.map f ≫ e.hom = e.hom ≫ G.map f)
    (m n : ℕ) (f : FiniteConstantModel.freeScalars A m ⟶
      FiniteConstantModel.freeScalars A n) :
    F.map f ≫ (scalarFreeComparison F G e n).hom =
      (scalarFreeComparison F G e m).hom ≫ G.map f := by
  let f' := (scalarBiproductIso m).inv ≫ f ≫ (scalarBiproductIso n).hom
  have h : (F.mapBiproduct (fun _ : Fin m ↦ scalarRegular A)).inv ≫ F.map f' ≫
      (F.mapBiproduct (fun _ : Fin n ↦ scalarRegular A)).hom ≫
        (biproduct.mapIso (fun _ : Fin n ↦ e)).hom =
      (biproduct.mapIso (fun _ : Fin m ↦ e)).hom ≫
        (G.mapBiproduct (fun _ : Fin m ↦ scalarRegular A)).inv ≫ G.map f' ≫
          (G.mapBiproduct (fun _ : Fin n ↦ scalarRegular A)).hom := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc, biproduct.mapIso_hom, biproduct.map_π,
      biproduct.ι_map_assoc, Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
      biproduct.ι_desc_assoc, biproduct.lift_π, biproduct.lift_π_assoc]
    simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc] using
      he (biproduct.ι (fun _ : Fin m ↦ scalarRegular A) j ≫ f' ≫
        biproduct.π (fun _ : Fin n ↦ scalarRegular A) k)
  apply (cancel_epi (F.map (scalarBiproductIso m).inv)).mp
  apply (cancel_epi (F.mapBiproduct (fun _ : Fin m ↦ scalarRegular A)).inv).mp
  apply (cancel_mono (G.map (scalarBiproductIso n).hom)).mp
  apply (cancel_mono (G.mapBiproduct (fun _ : Fin n ↦ scalarRegular A)).hom).mp
  simp only [scalarFreeComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [F.map_id, G.map_id]
  simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id, Iso.inv_hom_id_assoc]
  exact h

private theorem scalarPresentationComparison
    (e : F.obj (scalarRegular A) ≅ G.obj (scalarRegular A))
    (he : ∀ f : scalarRegular A ⟶ scalarRegular A,
      F.map f ≫ e.hom = e.hom ≫ G.map f)
    (N : ModuleCat.{u + 1} A) (hN : Module.FinitePresentation A N) :
    Nonempty (F.obj N ≅ G.obj N) := by
  have := hN
  obtain ⟨m, n, f, ⟨en⟩⟩ := ContinuousScalarPresentation.ordinary_presentation A N
  exact ⟨F.mapIso en ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) (G.map f)
      (scalarFreeComparison F G e m) (scalarFreeComparison F G e n)
      (scalarFreeComparison_natural F G e he m n f) ≪≫
    (PreservesCokernel.iso G f).symm ≪≫ (G.mapIso en).symm⟩

end FinitePresentationComparison

/-- The fixed integral section comparison sends a finitely presented ordinary scalar
module, extended from the condensed point, to its completed constant realization.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the scalar
comparison in the integral constructibility bridge.
(auxiliary; not a blueprint node).

Proof: choose a finite presentation of N by free scalar modules. The two realizations
preserve finite sums and cokernels: constant sheafification, extension of scalars,
and inverse image do, and section comparison and coefficient restriction are
equivalences. On the regular scalar module identify both values with the coefficient
module. At every positive uniformizer quotient, the prescribed coefficient maps send
an element to its constant section. Joint monicity of the completion projections
identifies the resulting maps on the completed regular module. This identification
commutes with scalar endomorphisms: evaluation of a constant function at the singleton
returns that scalar. The ULift change sends a lifted scalar to the same element.
Extend the regular-module comparison to the finite free terms by biproducts. Checking
each matrix entry identifies the two presentation maps. Preservation of their
cokernels and cokernel uniqueness give the asserted isomorphism on N. Empty matrices,
torsion modules and empty schemes are included. -/
theorem integralSectionScalarModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (hN : Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) N) :
    Nonempty ((SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
      ((integralSectionFunctor l E X).obj
        (((upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)).obj
          ((let A := Padic.coefficientExtensionIntegers l E
            letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
            continuousScalarFunctor A).obj N))) ≅
      (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj
        ((ModuleCat.restrictScalars
          (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
            Padic.coefficientExtensionIntegers l E).toRingHom).obj N)) := by
  have hF := (IntegralSectionScalars.finiteColimits l E X).1
  have hG := (IntegralSectionScalars.finiteColimits l E X).2
  have haF : (IntegralSectionScalars.sectionRealization l E X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ hF
  have haG : (IntegralSectionScalars.completedRealization l E X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ hG
  obtain ⟨e, he⟩ := IntegralSectionScalars.regularComparison l E X
  have h := scalarPresentationComparison
    (IntegralSectionScalars.sectionRealization l E X)
    (IntegralSectionScalars.completedRealization l E X) e he N hN
  unfold IntegralSectionScalars.sectionRealization
    IntegralSectionScalars.completedRealization at h
  exact h

end AlgebraicGeometry.ProEtale
