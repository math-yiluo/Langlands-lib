/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsSequentialColimit

/-! # The localization telescope of integral continuous coefficients -/

@[expose] public section

universe u v w x
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The localization-unit cocone for an additive adjunction whose localized object
has invertible multiplication by ℓ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(auxiliary; not a blueprint node). -/
noncomputable def scalarLocalizationUnitCocone
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {L : A ⥤ B} {U : B ⥤ A} [U.Additive] (adj : L ⊣ U) (K : A)
    [IsIso (ℓ • 𝟙 (L.obj K))] : Cocone (Mod.smulSequence K ℓ) :=
  let t : End (L.obj K) := .of (inv (ℓ • 𝟙 (L.obj K)))
  Mod.smulSequenceCocone ℓ (fun n ↦ adj.unit.app K ≫ U.map (t ^ n).asHom) fun n ↦ by
    have ht : (ℓ • 𝟙 (L.obj K)) ≫ (t ^ (n + 1)).asHom = (t ^ n).asHom := by
      rw [pow_succ, End.mul_asHom, ← Category.assoc]
      simp only [t, IsIso.hom_inv_id, Category.id_comp]
    rw [← Preadditive.comp_nsmul, ← U.map_nsmul, ← ht, Preadditive.nsmul_comp,
      Category.id_comp]

/-- The unit of integral localization, with its nth leg divided by ℓⁿ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(auxiliary; not a blueprint node). -/
noncomputable def integralLocalizationCocone (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) :
    Cocone (Mod.smulSequence K ℓ) := by
  have h := derived_nsmul_isIso ℓ E X ((integralScalarExtension ℓ E X).obj K)
  change IsIso (ℓ • 𝟙
    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).leftDerivedFunctor.obj K)) at h
  exact scalarLocalizationUnitCocone ℓ
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (integralScalarMap ℓ E) X)) K

/-- The same telescope in the universe of the small pro-etale sites.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(auxiliary; not a blueprint node). -/
abbrev integralLocalizationLiftedSequence {C : Type v} [Category.{w} C] [Preadditive C]
    (K : C) : ULift.{x} ℕ ⥤ C :=
  (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor ⋙ Mod.smulSequence K ℓ

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Reindex the unit telescope along the order equivalence with the lifted natural numbers.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
noncomputable def integralLocalizationLiftedCocone (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) :
    Cocone (integralLocalizationLiftedSequence.{_, _, x} ℓ K) :=
  (integralLocalizationCocone ℓ E X K).whisker
    (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor

end

end AlgebraicGeometry.ProEtale.CondensedRing
