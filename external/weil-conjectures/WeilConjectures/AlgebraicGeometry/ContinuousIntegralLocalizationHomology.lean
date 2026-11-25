/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationColimitTransport
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # Cohomology of the integral localization telescope -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Cohomology carries the localization-unit telescope of a bounded-below integral
complex to a colimit.
Source: Bhatt--Scholze, Lemma 6.8.2, and exactness of filtered colimits of module sheaves.
(auxiliary; not a blueprint node).
Proof. Use the strict coefficient telescope model. Its good truncation is already
an isomorphism because every term is zero below the common bound. Filtered colimits
are exact in module sheaves, so termwise cohomology preserves this colimit. The
factorization of derived cohomology through complexes gives the claimed cocone. -/
theorem integralLocalization_homology_isColimit (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.plus K) (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) X)) q).mapCocone
      (integralLocalizationLiftedCocone.{u, u + 1} ℓ E X K))) := by
  have : HasColimitsOfShape (ULift.{u + 1} ℕ)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  obtain ⟨m⟩ := exists_integralLocalization_complex_model ℓ E X K hK
  unfold integralLocalizationLiftedCocone
  apply localizationCocone_isColimit_of_model ℓ K _ m
  intro C a hC
  have : HasColimitsOfShape (ULift.{u + 1} ℕ)
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) ℤ) := inferInstance
  let : IsFiltered (ULift.{u + 1} ℕ) :=
    IsFiltered.of_equivalence (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
  let D := integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ C
  let π := Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)))
  have : ∀ i, IsIso (π.app i) := fun i ↦ by
    change IsIso (HomologicalComplex.πTruncGE C (ComplexShape.embeddingUpIntGE a))
    exact (HomologicalComplex.isIso_πTruncGE_iff C _).2 hC
  have : IsIso π := NatIso.isIso_of_isIso_app π
  have : HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X))) := HasColimitsOfShape.has_colimit _
  have hc : IsColimit (condensedContinuityCocone D a) :=
    (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
  have : PreservesColimitsOfShape (ULift.{u + 1} ℕ)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) X)) q) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) q).symm
  exact ⟨isColimitOfPreserves _ hc⟩

end AlgebraicGeometry.ProEtale.CondensedRing
