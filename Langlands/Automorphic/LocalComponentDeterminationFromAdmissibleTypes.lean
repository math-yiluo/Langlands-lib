import Langlands.Automorphic.LocalComponentDeterminationReverse

/-! # Determination from common admissible local components -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace Langlands.Automorphic

open Langlands.Global
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open FreeMonoidGenerators

attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup localComponentGeneralLinearTopology

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- Common irreducible admissible local types at all places determine the full
operator equivalence of two irreducible subquotients. -/
theorem nonempty_equivalence_of_common_admissible_localComponents {r : ℕ}
    (Q Q' : IrreducibleOperatorSubquotient F r)
    (hfin : ∀ v : FinitePlace F, ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      Q.subquotient.IsFinitePlaceIsotypic v A.obj.representation ∧
        Q'.subquotient.IsFinitePlaceIsotypic v A.obj.representation)
    (hreal : ∀ v : RP, ∃ (V : ModuleCat.{u} ℂ)
      (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsRealGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
        Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsRealPlaceIsotypic v ρ π)
    (hcomplex : ∀ v : CP, ∃ (V : ModuleCat.{u} ℂ)
      (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsComplexGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
        Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
        Q'.subquotient.IsComplexPlaceIsotypic v ρ π) :
    Nonempty (Q.Equivalence Q') := by
  choose A hQf hQ'f using hfin
  choose Vr ρr πr hGKr hirrR hadmR hQr hQ'r using hreal
  choose Vc ρc πc hGKc hirrC hadmC hQc hQ'c using hcomplex
  let D : PlaceData F (r + 1) :=
    ⟨fun v => ModuleCat.of ℂ (A v).obj, fun v => (A v).obj.representation, Vr, ρr, πr, Vc, ρc, πc⟩
  have hfinite (v : FinitePlace F) := finitePlace_isCommonType Q Q' v ⟨A v, hQf v⟩
    (A v).obj.representation (A v).property.1 (hQf v) (hQ'f v)
  have hcommon : ∀ i, IsCommonType (D.localRep i) (Q.subquotient.placeRep i)
      (Q'.subquotient.placeRep i) := by
    rintro (v | v | v)
    · exact (hfinite v).1
    · exact realPlace_isCommonType Q Q' v
        ⟨Vr v, ρr v, πr v, hGKr v, hirrR v, hadmR v, hQr v⟩
        (ρr v) (πr v) (hirrR v) (hQr v) (hQ'r v)
    · exact complexPlace_isCommonType Q Q' v
        ⟨Vc v, ρc v, πc v, hGKc v, hirrC v, hadmC v, hQc v⟩
        (ρc v) (πc v) (hirrC v) (hQc v) (hQ'c v)
  have hsph : ∀ᶠ i in Filter.cofinite, ∃ w₀ : D.carrier i, ∀ w : D.carrier i,
      (∀ h ∈ placeSpherical F (r + 1) i, D.localRep i h w = w) → ∃ c : ℂ, w = c • w₀ := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_range Sum.inr).subset ?_
    rintro (v | w) hi
    · refine absurd ?_ hi
      obtain ⟨w₀, hw₀⟩ := (hfinite v).2
      exact ⟨w₀, fun w hw => hw₀ w fun g hg => hw (FreeMonoid.of g) (of_mem_placeSpherical hg)⟩
    · exact ⟨w, rfl⟩
  have : ∀ i, (D.localRep i).IsIrreducible := fun i => (hcommon i).1
  obtain ⟨e, he⟩ := CommutingFamily.exists_linearEquiv_of_isotypic Q.subquotient.placeRep
    Q.subquotient.placeRep_commuting Q'.subquotient.placeRep Q'.subquotient.placeRep_commuting
    (Q.subquotient.isJointlyIrreducible_placeRep Q.irreducible)
    (Q'.subquotient.isJointlyIrreducible_placeRep Q'.irreducible) D.localRep
    (fun i => (hcommon i).2.1) (fun i => (hcommon i).2.2.1) (fun i => (hcommon i).2.2.2)
    (placeSpherical F (r + 1)) hsph Q.subquotient.placeRep_eventually_fixed
    Q'.subquotient.placeRep_eventually_fixed
  have hgen : ∀ i a x, e (Q.subquotient.placeGeneratorAction i a x) =
      Q'.subquotient.placeGeneratorAction i a (e x) :=
    fun i a x => he i (FreeMonoid.of a) x
  exact ⟨Q.subquotient.equivalenceOfPlaceComm Q'.subquotient e
    (fun v g x => hgen (.inl v) g x)
    (fun v k x => hgen (.inr (.inl v)) (ULift.up (Sum.inl k)) x)
    (fun v X x => hgen (.inr (.inl v)) (ULift.up (Sum.inr X)) x)
    (fun v k x => hgen (.inr (.inr v)) (ULift.up (Sum.inl k)) x)
    (fun v X x => hgen (.inr (.inr v)) (ULift.up (Sum.inr X)) x)⟩

end Langlands.Automorphic
