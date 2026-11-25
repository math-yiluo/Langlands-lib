/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationColimitTransport

/-! # Applying qcqs continuity to the integral localization telescope -/

@[expose] public section

universe u v w
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The qcqs derived pushforward carries the localization-unit telescope to a colimit
on each cohomology sheaf.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2.
(auxiliary; not a blueprint node).
Proof: the strict coefficient telescope model has one lower bound. Apply the existing
qcqs continuity theorem to that model, then transport its colimit cocone along the
representative isomorphism and the specified localization leg equations. -/
theorem integralLocalization_push_homology_isColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.plus K) (q : ℤ) :
    Nonempty (IsColimit (((lowerStar (integralCoeff ℓ E) f).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q).mapCocone
      (integralLocalizationLiftedCocone.{u, u + 1} ℓ E X K))) := by
  have : HasColimitsOfShape (ULift.{u + 1} ℕ)
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  obtain ⟨m⟩ := exists_integralLocalization_complex_model ℓ E X K hK
  unfold integralLocalizationLiftedCocone
  apply localizationCocone_isColimit_of_model ℓ K _ m
  intro C a hC
  have : HasColimitsOfShape (ULift.{u + 1} ℕ)
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) ℤ) := inferInstance
  let : IsFiltered (ULift.{u + 1} ℕ) :=
    IsFiltered.of_equivalence (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
  have ha (i : ULift.{u + 1} ℕ) (n : ℤ) (hn : n < a) :
      IsZero (((integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C).obj i).homology
        n) := by
    have := hC
    exact C.isZero_of_isGE a n hn
  have h := condensed_qcqs_pushforward_continuity (integralCoeff ℓ E) f
    (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C) a ha q
  let D := integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C
  let T := DerivedCategory.Q ⋙ (lowerStar (integralCoeff ℓ E) f).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ q
  have : HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X))) := HasColimitsOfShape.has_colimit _
  have : HasColimit (D ⋙ T) := HasColimitsOfShape.has_colimit _
  have : IsIso (colimit.desc (D ⋙ T) (T.mapCocone (condensedContinuityCocone D a))) := h
  exact ⟨IsColimit.ofPointIso (colimit.isColimit (D ⋙ T)) (i := by exact h)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
