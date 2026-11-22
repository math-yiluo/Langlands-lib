import Langlands.Global.AdelicEisensteinBruhatAbsoluteBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuity of the actual unfolded Eisenstein terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth Langlands.Automorphic.GroupSchemeFunctions

private theorem continuousIntegral_of_majorant
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [FirstCountableTopology Y]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (m : Measure X) (f : Y → X → ℂ) (W : Y → ℝ) (B : X → ℝ)
    (hf : Continuous fun z : X × Y => f z.2 z.1)
    (hW : Continuous W) (hB : Integrable B m) (hB₀ : ∀ x, 0 ≤ B x)
    (hbound : ∀ x y, ‖f y x‖ ≤ B x * W y) :
    (∀ y, Integrable (f y) m) ∧ Continuous (fun y => ∫ x, f y x ∂m) := by
  have hv (y : Y) : Continuous (f y) := hf.comp (continuous_id.prodMk continuous_const)
  have hy (x : X) : Continuous (fun y => f y x) := hf.comp (continuous_const.prodMk continuous_id)
  refine ⟨fun y => (hB.mul_const (W y)).mono' (hv y).aestronglyMeasurable
    (Eventually.of_forall fun x => hbound x y), continuous_iff_continuousAt.2 fun y => ?_⟩
  have hnear : {z | W z < W y + 1} ∈ 𝓝 y :=
    (isOpen_lt hW continuous_const).mem_nhds (show W y < W y + 1 from lt_add_one (W y))
  change ContinuousAt (fun z => ∫ x, f z x ∂m) y
  refine tendsto_integral_filter_of_dominated_convergence (fun x => B x * (W y + 1))
    (Eventually.of_forall fun z => (hv z).aestronglyMeasurable) ?_ (hB.mul_const _) ?_
  · filter_upwards [hnear] with z hz
    exact Eventually.of_forall fun x => (hbound x z).trans
      (mul_le_mul_of_nonneg_left (le_of_lt hz) (hB₀ x))
  · exact Eventually.of_forall fun x => (hy x).continuousAt

variable {F : Type u} [Field F] [NumberField F]
  {G P Q V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine V.X.left]
  (p : P ⟶ G) (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (w : AdelicGroupPoints F G)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "Points" => AdelicGroupPoints F G
local notation "j" => (iV ≫ q)
local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
local notation "Γ" => stabilizerRationalSubgroup F p j w
local notation "ν" => stabilizerMeasure F p j w

/-- A polynomial-weighted integrable stabilizer majorant gives absolute
integrability at every external argument and continuity of the integral. -/
def EisensteinStabilizerContinuityStatement : Prop :=
  0 < N → ∀ Φ : Points → ℂ, Continuous Φ →
    IsLeftInvariantUnder F G (rationalImage F p) Φ →
    ∀ (B : LeftCosetSpace Γ → ℝ) (d : ℝ), Integrable B ν → (∀ v, 0 ≤ B v) → 0 ≤ d →
      (∀ v g, ‖eisensteinStabilizerIntegrand p q iV w Φ g v‖ ≤ B v * adelicHeight F G rho g ^ d) →
      (∀ g, Integrable (eisensteinStabilizerIntegrand p q iV w Φ g) ν) ∧
        Continuous (fun g => ∫ v, eisensteinStabilizerIntegrand p q iV w Φ g v ∂ν)

set_option maxHeartbeats 850000 in
theorem eisensteinStabilizerContinuity : EisensteinStabilizerContinuityStatement p q iV w rho := by
  intro hN Φ hΦc hΦ B d hB hB₀ hd hbound
  let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace Vₐ := hClosed.locallyCompactSpace
  let : PolishSpace Vₐ := hClosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_stabilizerRationalSubgroup F p j w)
  have hW : Continuous (fun g : Points => adelicHeight F G rho g ^ d) :=
    (continuous_adelicHeight F G rho hN).rpow_const fun _ => Or.inr hd
  exact continuousIntegral_of_majorant ν (eisensteinStabilizerIntegrand p q iV w Φ)
    (fun g => adelicHeight F G rho g ^ d) B
    (continuous_eisensteinStabilizerIntegrand p q iV w Φ hΦ hΦc) hW hB hB₀ hbound

end Langlands.Global
