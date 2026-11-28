import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.ImaginaryAxisAveraging
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Continuity and integrability on the characteristic truncation region -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Metric Set Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  AdelicSiegelFactors Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The characteristic pairing of a jointly continuous family and a fixed continuous form is
continuous in the spectral coordinates on a compact characteristic region. Both inputs are
left invariant under the rational points. The conclusion includes absolute integrability. -/
def CharacteristicPairingContinuityStatement : Prop :=
  ∀ {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅))
    (T₀ T : V fam.T) (z : fam.positiveSplitComponent fam.top) {n : ℕ}
    (E : (Fin n → ℝ) → AdelicGroupPoints F G → ℂ) (Φ : AdelicGroupPoints F G → ℂ),
    IsCompact (fam.truncationRegion hK C T₀ T) →
    Continuous (Function.uncurry E) → Continuous Φ →
    (∀ x, IsLeftInvariantUnder F G (rationalSubgroup F G) (E x)) →
    IsLeftInvariantUnder F G (rationalSubgroup F G) Φ →
    Continuous (fun x => fam.truncatedPairing hK C T₀ T z (E x) Φ) ∧
    ∀ x, IntegrableOn (fam.truncatedPairingIntegrand z (E x) Φ)
      (fam.truncationRegion hK C T₀ T) (normOneRationalQuotientHaarMeasure F G)

/-- Descend the product to the quotient and dominate the integral by a constant on every compact
ball of spectral parameters times the characteristic region. -/
theorem characteristicPairingContinuity : fam.CharacteristicPairingContinuityStatement := by
  intro K hK C T₀ T z n E Φ hcompact hE hΦ hEinv hΦinv
  let H := normOneSubgroup F G
  let Γ := rationalNormOneSubgroup F G
  let S := fam.truncationRegion hK C T₀ T
  let measure := normOneRationalQuotientHaarMeasure F G
  let p (g : H) : AdelicGroupPoints F G := g.val * fam.centralPoint z
  let f (x : Fin n → ℝ) (g : H) := E x (p g) * starRingEnd ℂ (Φ (p g))
  have hp : Continuous p := continuous_subtype_val.mul continuous_const
  have hf : Continuous (Function.uncurry f) :=
    (hE.comp (continuous_fst.prodMk (hp.comp continuous_snd))).mul
      (Complex.continuous_conj.comp (hΦ.comp (hp.comp continuous_snd)))
  have hfinv (x : Fin n → ℝ) (c : H) (hc : c ∈ Γ) (g : H) : f x (c * g) = f x g := by
    have hc' : c.val ∈ rationalSubgroup F G := (rationalNormOneSubgroupInclusion F G ⟨c, hc⟩).2
    have hmul : p (c * g) = c.val * p g := mul_assoc _ _ _
    simp only [f, hmul, hEinv x c.val hc', hΦinv c.val hc']
  let I (x : Fin n → ℝ) := fam.truncatedPairingIntegrand z (E x) Φ
  have hI : Continuous (Function.uncurry I) := by
    change Continuous (fun q : (Fin n → ℝ) × LeftCosetSpace Γ => f q.1 q.2.out)
    have hjoint : ContinuousOn (fun q : (Fin n → ℝ) × H => f q.1 q.2) (univ ×ˢ univ) :=
      hf.continuousOn
    have hc := ImaginaryAxis.continuousOn_out_of_invariant Γ f univ isOpen_univ hjoint
      (fun x _ => hfinv x)
    simpa only [univ_prod_univ, continuousOn_univ] using hc
  have hIc (x : Fin n → ℝ) : Continuous (I x) :=
    hI.comp (continuous_const.prodMk continuous_id)
  have hIint (x : Fin n → ℝ) : IntegrableOn (I x) S measure :=
    (hIc x).continuousOn.integrableOn_compact hcompact
  refine ⟨?_, hIint⟩
  let : IsFiniteMeasure (measure.restrict S) := isFiniteMeasure_restrict.mpr
    hcompact.measure_lt_top.ne
  change Continuous (fun x => ∫ y, I x y ∂(measure.restrict S))
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hcompact).exists_bound_of_continuousOn
    hI.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B)
    (.of_forall fun x => (hIint x).aestronglyMeasurable) ?_ (integrable_const B) ?_
  · filter_upwards [closedBall_mem_nhds x₀ zero_lt_one] with x hx
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with y hy
    exact hB (x, y) ⟨hx, hy⟩
  · exact .of_forall fun y => (hI.comp (continuous_id.prodMk continuous_const)).continuousAt

end Langlands.Global.StandardParabolicFamily
