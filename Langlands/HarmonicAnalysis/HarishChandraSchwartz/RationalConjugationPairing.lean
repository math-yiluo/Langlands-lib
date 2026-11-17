import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.Analysis.Local.NormalSubgroupHaarModulus
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Conjugation pairings and descent to the actual central quotient

The integral is totalized. Central descent is pointwise and requires no convergence.
Additivity has explicit integrability premises; quotient measurability and convergence
are separate analytic obligations.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

universe u uG

section Functions

variable {Γ : Type uG} [Group Γ] [MeasurableSpace Γ]

/-- The bilinear, non-Hermitian integrand of Waldspurger VIII.3. -/
def conjugationIntegrand (f₁ f₂ : Γ → ℂ) (h g : Γ) : ℂ :=
  f₁ (h * g * h⁻¹) * f₂ g

/-- The total Bochner integral. Its definition alone asserts no convergence. -/
def conjugationPairing (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) (h : Γ) : ℂ :=
  ∫ g, conjugationIntegrand f₁ f₂ h g ∂μ

omit [MeasurableSpace Γ] in
/-- Central multiplication leaves the conjugation argument unchanged. -/
theorem conjugationIntegrand_central_mul (f₁ f₂ : Γ → ℂ) {z : Γ}
    (hz : z ∈ Subgroup.center Γ) (h g : Γ) :
    conjugationIntegrand f₁ f₂ (z * h) g = conjugationIntegrand f₁ f₂ h g := by
  have hc := Subgroup.mem_center_iff.mp hz (h * g * h⁻¹)
  have he : (z * h) * g * (z * h)⁻¹ = h * g * h⁻¹ := by
    calc
      (z * h) * g * (z * h)⁻¹ = z * (h * g * h⁻¹) * z⁻¹ := by group
      _ = (h * g * h⁻¹) * z * z⁻¹ := by rw [hc]
      _ = h * g * h⁻¹ := by group
  simp only [conjugationIntegrand, he]

/-- Pointwise central invariance holds for the totalized integral as well. -/
theorem conjugationPairing_central_mul (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) {z : Γ}
    (hz : z ∈ Subgroup.center Γ) (h : Γ) :
    conjugationPairing μ f₁ f₂ (z * h) = conjugationPairing μ f₁ f₂ h := by
  unfold conjugationPairing
  exact integral_congr_ae (Filter.Eventually.of_forall
    (conjugationIntegrand_central_mul f₁ f₂ hz h))

/-- First-variable additivity is asserted on the displayed convergence domain. -/
theorem conjugationPairing_add_left (μ : Measure Γ) (f₁ f₁' f₂ : Γ → ℂ) (h : Γ)
    (h₁ : Integrable (conjugationIntegrand f₁ f₂ h) μ)
    (h₁' : Integrable (conjugationIntegrand f₁' f₂ h) μ) :
    conjugationPairing μ (f₁ + f₁') f₂ h =
      conjugationPairing μ f₁ f₂ h + conjugationPairing μ f₁' f₂ h := by
  simpa only [conjugationPairing, conjugationIntegrand, Pi.add_apply, add_mul]
    using integral_add h₁ h₁'

/-- Second-variable additivity also retains both convergence premises. -/
theorem conjugationPairing_add_right (μ : Measure Γ) (f₁ f₂ f₂' : Γ → ℂ) (h : Γ)
    (h₂ : Integrable (conjugationIntegrand f₁ f₂ h) μ)
    (h₂' : Integrable (conjugationIntegrand f₁ f₂' h) μ) :
    conjugationPairing μ f₁ (f₂ + f₂') h =
      conjugationPairing μ f₁ f₂ h + conjugationPairing μ f₁ f₂' h := by
  simpa only [conjugationPairing, conjugationIntegrand, Pi.add_apply, mul_add]
    using integral_add h₂ h₂'

/-- Constant multiplication commutes with the total Bochner integral. -/
theorem conjugationPairing_smul_left (μ : Measure Γ) (c : ℂ) (f₁ f₂ : Γ → ℂ) (h : Γ) :
    conjugationPairing μ (c • f₁) f₂ h = c * conjugationPairing μ f₁ f₂ h := by
  simp only [conjugationPairing, conjugationIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

/-- Constant multiplication in the second variable has the same formula. -/
theorem conjugationPairing_smul_right (μ : Measure Γ) (c : ℂ) (f₁ f₂ : Γ → ℂ) (h : Γ) :
    conjugationPairing μ f₁ (c • f₂) h = c * conjugationPairing μ f₁ f₂ h := by
  simp only [conjugationPairing, conjugationIntegrand, Pi.smul_apply, smul_eq_mul,
    mul_left_comm (f₁ _) c]
  exact integral_const_mul _ _

/-- Descent to actual left cosets of a specified central subgroup. -/
def leftConjugationPairing (A : Subgroup Γ) (hA : A ≤ Subgroup.center Γ)
    (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) : LeftQuotient A → ℂ :=
  descend A (conjugationPairing μ f₁ f₂)
    (fun a h => conjugationPairing_central_mul μ f₁ f₂ (hA a.property) h)

@[simp] theorem leftConjugationPairing_mk (A : Subgroup Γ) (hA : A ≤ Subgroup.center Γ)
    (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) (h : Γ) :
    leftConjugationPairing A hA μ f₁ f₂ (Quotient.mk _ h) =
      conjugationPairing μ f₁ f₂ h := rfl

/-- Evaluation at any representative, including `Quotient.out`. -/
theorem leftConjugationPairing_eq_out (A : Subgroup Γ) (hA : A ≤ Subgroup.center Γ)
    (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) (q : LeftQuotient A) :
    leftConjugationPairing A hA μ f₁ f₂ q = conjugationPairing μ f₁ f₂ q.out := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

/-- The value is independent of the chosen group representative. -/
theorem conjugationPairing_eq_of_leftQuotient_eq (A : Subgroup Γ)
    (hA : A ≤ Subgroup.center Γ) (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) {h k : Γ}
    (hhk : (Quotient.mk _ h : LeftQuotient A) = Quotient.mk _ k) :
    conjugationPairing μ f₁ f₂ h = conjugationPairing μ f₁ f₂ k :=
  congrArg (leftConjugationPairing A hA μ f₁ f₂) hhk

section RightQuotient

variable [TopologicalSpace Γ]
  (A : Subgroup Γ) [A.Normal] (hA : A ≤ Subgroup.center Γ)

/-- The realization on `Γ / A` uses the published same-representative homeomorphism. -/
def rightConjugationPairing (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) : Γ ⧸ A → ℂ :=
  leftConjugationPairing A hA μ f₁ f₂ ∘ (normalLeftQuotientHomeomorph A).symm

@[simp] theorem rightConjugationPairing_homeomorph (μ : Measure Γ) (f₁ f₂ : Γ → ℂ)
    (q : LeftQuotient A) :
    rightConjugationPairing A hA μ f₁ f₂ (normalLeftQuotientHomeomorph A q) =
      leftConjugationPairing A hA μ f₁ f₂ q := by
  simp only [rightConjugationPairing, Function.comp_apply, Homeomorph.symm_apply_apply]

@[simp] theorem rightConjugationPairing_mk (μ : Measure Γ) (f₁ f₂ : Γ → ℂ) (h : Γ) :
    rightConjugationPairing A hA μ f₁ f₂ (h : Γ ⧸ A) = conjugationPairing μ f₁ f₂ h := by
  simpa only [normalLeftQuotientHomeomorph_mk, leftConjugationPairing_mk]
    using rightConjugationPairing_homeomorph A hA μ f₁ f₂ (Quotient.mk _ h)

variable [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  [MeasurableSpace (Γ ⧸ A)] [BorelSpace (Γ ⧸ A)]

/-- Explicit transport of the left-quotient measure. -/
def conjugationRightQuotientMeasure (ν : Measure (LeftQuotient A)) : Measure (Γ ⧸ A) :=
  ν.map (normalLeftQuotientHomeomorph A)

/-- True Bochner integrability, including a.e. measurability, is equivalent on the two
quotients for the displayed transported measure. No convergence is assumed or concluded. -/
theorem integrable_rightConjugationPairing_iff (μ : Measure Γ) (f₁ f₂ : Γ → ℂ)
    (ν : Measure (LeftQuotient A)) :
    Integrable (rightConjugationPairing A hA μ f₁ f₂) (conjugationRightQuotientMeasure A ν) ↔
      Integrable (leftConjugationPairing A hA μ f₁ f₂) ν := by
  rw [conjugationRightQuotientMeasure,
    (normalLeftQuotientHomeomorph A).measurableEmbedding.integrable_map_iff]
  simp only [Function.comp_def, rightConjugationPairing_homeomorph]

/-- The total integrals agree under the same transport. -/
theorem integral_rightConjugationPairing (μ : Measure Γ) (f₁ f₂ : Γ → ℂ)
    (ν : Measure (LeftQuotient A)) :
    ∫ q, rightConjugationPairing A hA μ f₁ f₂ q ∂conjugationRightQuotientMeasure A ν =
      ∫ q, leftConjugationPairing A hA μ f₁ f₂ q ∂ν := by
  rw [conjugationRightQuotientMeasure,
    (normalLeftQuotientHomeomorph A).measurableEmbedding.integral_map]
  simp only [rightConjugationPairing_homeomorph]

end RightQuotient
end Functions

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The actual Schwartz-function pairing, with its group measure explicit. -/
abbrev rationalConjugationPairing (muG : Measure (rationalPoints G))
    (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ) : rationalPoints G → ℂ :=
  conjugationPairing muG (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ)

/-- Pointwise invariance under the actual split centre, without convergence assumptions. -/
theorem rationalConjugationPairing_splitCenter_mul (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (a : (rationalPoints.map s).range) (h : rationalPoints G) :
    rationalConjugationPairing hKc hPK ρ muG f₁ f₂ ((a : rationalPoints G) * h) =
      rationalConjugationPairing hKc hPK ρ muG f₁ f₂ h :=
  conjugationPairing_central_mul muG _ _ (hs.isCentralSplitTorus.isCentral.range_le_center a.2) h

/-- The genuine `A_G(F) \ G(F)` realization, for the displayed split component. -/
def rationalLeftConjugationPairing (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ) :
    LeftQuotient (rationalPoints.map s).range → ℂ :=
  leftConjugationPairing _ hs.isCentralSplitTorus.isCentral.range_le_center muG
    (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ)

@[simp] theorem rationalLeftConjugationPairing_mk (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (h : rationalPoints G) :
    rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂ (Quotient.mk _ h) =
      rationalConjugationPairing hKc hPK ρ muG f₁ f₂ h := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The actual split-central point image is normal, by centrality alone. -/
theorem rationalSplitCenter_normal (s : T.toGrp ⟶ G) (hs : IsSplitComponent s) :
    (rationalPoints.map s).range.Normal :=
  Subgroup.normal_of_le_center hs.isCentralSplitTorus.isCentral.range_le_center

end Rational

end Langlands.HarishChandraSchwartz
