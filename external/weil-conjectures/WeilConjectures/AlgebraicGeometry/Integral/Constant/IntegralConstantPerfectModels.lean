/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import all WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedConstantModuleTensor
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Strict perfect models of completed constant realization

## References

* Bhatt--Scholze, Proposition 6.6.11 and the finite-projective step in Lemma 6.3.14
* Bhatt--Scholze, Proposition 6.6.11, and Lemma 6.3.14(1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.flatConstantModulesAbelian
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

namespace AlgebraicGeometry.Scheme

private def restrictionUnitIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · let eU := ((sheafToPresheaf (ProEt.topology X) RingCat).mapIso e).app U
    exact ModuleCat.restrictScalarsIsoOfEquiv eU.ringCatIsoToRingEquiv
  · intro U V f
    ext x
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) x

private def completedRegularIso (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    (integralConstantModule X d).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit ((adicLisseForget X).obj (pbcAdicCompletion X d)) := by
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  have := completedOne_isIso X dd
  unfold integralConstantModule
  exact (pbcRestrict (pbcCompletedComparison X d).inv).mapIso
    (asIso (completedKoszulOne X dd)).symm ≪≫
      restrictionUnitIso X ((adicLisseForget X).mapIso (pbcCompletedComparison X d)).symm

private def finiteProjectivePackage
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {A : Type r} [CommRing A] (R : Sheaf J RingCat.{r})
    (F : ModuleCat.{r} A ⥤ SheafOfModules.{r} R)
    [F.Additive] [PreservesFiniteLimits F]
    (e : F.obj (ModuleCat.of A A) ≅ SheafOfModules.unit R)
    (P : CochainComplex (ModuleCat.{r} A) ℤ)
    (hP : ∀ n, Module.Projective A (P.X n) ∧ Module.Finite A (P.X n)) :
    SheafOfModules.StrictPerfectCoefficientPackageOnSite R
      ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  have spl (n : ℤ) : ∃ k : ℕ,
      Nonempty (Retract (P.X n) (ModuleCat.of A (Fin k → A))) := by
    have := (hP n).1
    have := (hP n).2
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' A (P.X n)
    obtain ⟨g, hg⟩ := Module.projective_lifting_property f
      (LinearMap.id : P.X n →ₗ[A] P.X n) hf
    exact ⟨k, ⟨⟨ModuleCat.ofHom g, ModuleCat.ofHom f,
      by ext x; exact LinearMap.congr_fun hg x⟩⟩⟩
  choose k hk using spl
  let s (n : ℤ) := (hk n).some.map F
  let e' (n : ℤ) : F.obj (ModuleCat.of A (Fin (k n) → A)) ≅
      ∏ᶜ fun _ : Fin (k n) ↦ SheafOfModules.unit R :=
    F.mapIso (ModuleCat.piIsoPi (fun _ : Fin (k n) ↦ ModuleCat.of A A)).symm ≪≫
      PreservesProduct.iso F (fun _ : Fin (k n) ↦ ModuleCat.of A A) ≪≫
        Pi.mapIso (fun _ ↦ e)
  exact
    { N := k
      i n := (s n).i ≫ (e' n).hom
      p n := (e' n).inv ≫ (s n).r
      splitting n := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, (s n).retract]
        rfl }

/-- A completed constant perfect scalar object has a bounded finite-free-retract
complex over the completed coefficient sheaf. -/
theorem integralConstantDerived_strictPerfectModel
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P) :
    ∃ E : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
      Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget X).obj (pbcAdicCompletion X d)) E) ∧
      Nonempty ((integralConstantDerived X d).obj P ≅ DerivedCategory.Q.obj E) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let F := integralConstantModule X d
  have : PreservesFiniteLimits F := (integralConstantModule_exact X d).1
  have : PreservesFiniteColimits F := (integralConstantModule_exact X d).2
  obtain ⟨Q, a, b, ha, hb, hQ, ⟨e⟩⟩ := hP
  have := ha
  have := hb
  refine ⟨(F.mapHomologicalComplex (.up ℤ)).obj Q, ⟨a, b, ?_⟩,
    ⟨finiteProjectivePackage _ F (completedRegularIso X d) Q hQ⟩,
    ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app Q⟩⟩
  intro n hn
  apply F.map_isZero
  rcases hn with hn | hn
  · exact Q.isZero_of_isStrictlyGE a n hn
  · exact Q.isZero_of_isStrictlyLE b n hn

end AlgebraicGeometry.Scheme
