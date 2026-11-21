import Langlands.Global.AdelicNormOneDecomposition
import Langlands.Global.AdelicPositiveTorusCompatibility
import Langlands.TraceFormula.TwistedOrbital

/-! # Support control under positive-torus averaging -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration

universe u

section PositiveFinitePlace

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K)))
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)

/-- Translating by the intrinsic positive torus leaves each finite component
of an adelic point unchanged. -/
theorem atPlace_positivePointMap_mul (hT : IsSplitTorus T.toGrp)
    (v : FinitePlace K) (a : intrinsicSubgroup K T) (x : AdelicGroupPoints K G) :
    atPlace K G (.inr v) (positivePointMap K G T i a * x) = atPlace K G (.inr v) x := by
  have ha : atPlace K T.toGrp (.inr v) a.val = 1 := atFinitePlace_intrinsic K T hT v a
  rw [map_mul, positivePointMap_apply, atPlace_map, ha, map_one, one_mul]

variable (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)

/-- The norm-one component of an adelic point has its original finite
components. -/
theorem atPlace_normOneFactor (v : FinitePlace K) (x : AdelicGroupPoints K G) :
    atPlace K G (.inr v) (normOneFactor K G T i hi I e x : AdelicGroupPoints K G) =
      atPlace K G (.inr v) x := by
  have hT : IsSplitTorus T.toGrp := ⟨I, inferInstance, ⟨e⟩⟩
  exact (atPlace_positivePointMap_mul K G T i hT v (positiveFactor K G T i hi I e x)
    (normOneFactor K G T i hi I e x)).symm.trans
      (congrArg (atPlace K G (.inr v)) (positivePointMap_mul_normOneFactor K G T i hi I e x))

end PositiveFinitePlace

/-- A compact broad support in the adelic group gives a common compact
support bound in the norm-one group for the positive averages of all test
functions supported there. A nonzero averaged value preserves the finite
components of a point in the support of the test function. -/
def PositiveAverageOrbitSupportStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
    (_hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (Ω : Set (AdelicGroupPoints K G)), IsCompact Ω →
    ∃ Ω₁ : Set (normOneSubgroup K G), IsCompact Ω₁ ∧
      (∀ z ∈ Ω₁, ∃ y ∈ Ω, ∀ v : FinitePlace K,
        atPlace K G (.inr v) y = atPlace K G (.inr v) z) ∧
      ∀ (ρ : Measure (intrinsicSubgroup K T)) (f : AdelicGroupPoints K G → ℂ),
        Function.support f ⊆ Ω →
        let fOne : normOneSubgroup K G → ℂ := fun z ↦
          ∫ a, f (positivePointMap K G T i a * (z : AdelicGroupPoints K G)) ∂ρ
        (∀ z, fOne z ≠ 0 → z ∈ Ω₁ ∧ ∃ y ∈ Function.support f,
          ∀ v : FinitePlace K, atPlace K G (.inr v) y = atPlace K G (.inr v) z) ∧
        ∀ (θ : normOneSubgroup K G →* normOneSubgroup K G) (r : normOneSubgroup K G)
          [MeasurableSpace (LeftQuotient (twistedCentralizer θ r))]
          (ν : Measure (LeftQuotient (twistedCentralizer θ r))),
          twistedOrbitalIntegral θ r ν fOne ≠ 0 →
          ∃ x : normOneSubgroup K G,
            x⁻¹ * r * θ x ∈ Ω₁ ∧ ∃ y ∈ Function.support f,
              ∀ v : FinitePlace K, atPlace K G (.inr v) y =
                atPlace K G (.inr v) (x⁻¹ * r * θ x : normOneSubgroup K G)

theorem positiveAverageOrbitSupport : PositiveAverageOrbitSupportStatement.{u} := by
  classical
  intro K _ _ G _ T i hi _ I _ e Ω hΩ
  let R := normOneFactor K G T i hi I e
  let Ω₁ := R '' Ω
  refine ⟨Ω₁, hΩ.image (continuous_normOneFactor K G T i hi I e), ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact ⟨y, hy, fun v ↦ (atPlace_normOneFactor K G T i hi I e v y).symm⟩
  intro ρ f hΩf fOne
  have hvalue (z : normOneSubgroup K G) (hz : fOne z ≠ 0) :
      z ∈ Ω₁ ∧ ∃ y ∈ Function.support f, ∀ v : FinitePlace K,
        atPlace K G (.inr v) y = atPlace K G (.inr v) z := by
    obtain ⟨a, ha⟩ : ∃ a : intrinsicSubgroup K T,
        f (positivePointMap K G T i a * (z : AdelicGroupPoints K G)) ≠ 0 := by
      by_contra h
      apply hz
      have hzero (a : intrinsicSubgroup K T) :
          f (positivePointMap K G T i a * (z : AdelicGroupPoints K G)) = 0 := by
        by_contra ha
        exact h ⟨a, ha⟩
      change ∫ a, f (positivePointMap K G T i a * (z : AdelicGroupPoints K G)) ∂ρ = 0
      simp only [hzero, integral_zero]
    let y := positivePointMap K G T i a * (z : AdelicGroupPoints K G)
    have hy : R y = z :=
      congrArg Prod.snd ((normOneDecompositionEquiv K G T i hi I e).symm_apply_apply (a, z))
    exact ⟨⟨y, hΩf ha, hy⟩, y, ha,
      fun v ↦ (atPlace_normOneFactor K G T i hi I e v y).symm.trans
        (congrArg (fun w : normOneSubgroup K G ↦ atPlace K G (.inr v) w) hy)⟩
  refine ⟨hvalue, ?_⟩
  intro θ r _ ν hν
  obtain ⟨x, hx⟩ : ∃ x : normOneSubgroup K G, fOne (x⁻¹ * r * θ x) ≠ 0 := by
    by_contra h
    apply hν
    have hzero (q : LeftQuotient (twistedCentralizer θ r)) :
        twistedOrbitFunction θ r fOne q = 0 := by
      induction q using Quotient.inductionOn with
      | h x =>
        rw [twistedOrbitFunction_mk]
        by_contra hx
        exact h ⟨x, hx⟩
    rw [twistedOrbitalIntegral]
    simp only [hzero, integral_zero]
  exact ⟨x, hvalue _ hx⟩

end Langlands.TraceFormula
