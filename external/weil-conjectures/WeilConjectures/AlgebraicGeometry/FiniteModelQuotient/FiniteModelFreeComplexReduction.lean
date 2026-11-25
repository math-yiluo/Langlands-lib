/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelOrdinaryFreeComplex

/-! # Quotient reduction of a literal finite free model complex

Source: blueprint latest, integral ctf-equals-bc, Local models; Stacks 093M and 0G7E.
(blueprint: lem-sfb-finite-model-free-complex-reduction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private lemma flat_finite_biproduct (T : Scheme.{u}) (r : ℕ) :
    ObjectProperty.flat (⨁ fun _ : Fin r ↦ 𝟙_ (AdicCompletion.Modules l E T)) := by
  have h := ObjectProperty.flat_coproduct
    (fun _ : ULift.{u + 1} (Fin r) ↦ 𝟙_ (AdicCompletion.Modules l E T))
    (fun _ ↦ ObjectProperty.prop_unit _)
  exact ObjectProperty.prop_of_iso _
    ((Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ Iso.refl _)).symm ≪≫
      (biproduct.isoCoproduct _).symm) h

-- The derived reduction unfolds the two-term free model complex and its matrix.
/-- Derived reduction of the literal two-term free model complex keeps its matrix.

Source: blueprint latest, integral ctf-equals-bc, Local models; Stacks Tags 093M,
06YQ, 06YY and 0G7E (blueprint: lem-sfb-finite-model-free-complex-reduction).

Proof: the model functor takes the two scalar free modules to the corresponding
finite free modules over the pulled-back integral ring. Thus the literal double
complex is a bounded complex of flat modules and is K-flat, without any injectivity
assumption on its differential. Compute derived extension along the actual quotient
map on this complex. On a free module of rank r, the map sending a scalar tensor a
basis vector to the same quotient basis vector identifies extension with the free
quotient module of rank r. On the jth basis vector, the ith coordinate of the
extended differential is the residue of v i j. The normalized encoding sends the
quotient regular module to the constant regular module and these basis maps to the
constant basis maps, by its normalization on constant scalar sections. These term
isomorphisms therefore commute with the differentials and identify the reduced
complex with the constant realization of scalarComplex. Localize this cochain
isomorphism and apply the unit of the specified fixedDerived equivalence. The empty
basis gives zero terms, so the same argument includes either or both ranks zero.
-/
theorem free_complex_reduction (T : Scheme.{u}) (n : ℕ) (e : Encoding l E n T)
    (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    Nonempty
      ((AdicCompletion.derivedReduction l E T n).obj
        (DerivedCategory.Q.obj
          (HomologicalComplex.double
            ((FiniteConstantModel.modelFunctor (A l E) T).map
              (integralDifferential l E a b v))
            (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide))) ≅
        internalComplex l E T n a b v e) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := FiniteConstantModel.modelFunctor (A l E) T
  let K : CochainComplex (AdicCompletion.Modules l E T) ℤ :=
    HomologicalComplex.double (F.map (integralDifferential l E a b v))
      (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)
  have hfree (r : ℕ) : ObjectProperty.flat
      (F.obj (ModuleCat.of (A l E) (Fin r → ULift.{u + 1} (A l E)))) := by
    obtain ⟨er⟩ := FiniteConstantModel.modelFiniteFree (A l E) T r
    apply (ObjectProperty.flat.prop_iff_of_iso er).2
    change ObjectProperty.flat (⨁ fun _ : Fin r ↦ 𝟙_ (AdicCompletion.Modules l E T))
    exact flat_finite_biproduct l E T r
  have hK : ∀ i, ObjectProperty.flat (K.X i) := by
    intro i
    by_cases h₁ : i = -1
    · subst i
      exact (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.doubleXIso₀ _ _)).2 (hfree a)
    by_cases h₀ : i = 0
    · subst i
      exact (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.doubleXIso₁ _ _ (by decide))).2 (hfree b)
    exact ObjectProperty.flat_of_isZero
      (HomologicalComplex.isZero_double_X _ _ i h₁ h₀)
  have : K.IsStrictlyGE (-1) := (K.isStrictlyGE_iff _).2 (fun i hi ↦
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega))
  have : K.IsStrictlyLE 0 := (K.isStrictlyLE_iff _).2 (fun i hi ↦
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega))
  have hk := CochainComplex.kFlat_of_bounded_of_flat K (-1) 0 hK
  let H := Mod.extendScalars (AdicCompletion.quotient l E T n)
  have := H.isIso_leftDerivedFunctorCounit_app_of_kFlat K hk
  let L := (H.mapHomologicalComplex (.up ℤ)).obj K
  let d : H.leftDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj L :=
    H.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
      asIso (H.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app L
  have : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  obtain ⟨eOrd⟩ := ordinary_free_complex l E T n e a b v
  exact ⟨d ≪≫ e.fixedDerived.unitIso.app (DerivedCategory.Q.obj L) ≪≫
    e.fixedDerived.inverse.mapIso
      (((e.ordinary.trans e.fixed).functor.mapDerivedCategoryFactors.app L) ≪≫
        DerivedCategory.Q.mapIso eOrd)⟩

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
