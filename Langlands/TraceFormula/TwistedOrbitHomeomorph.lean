import Langlands.TraceFormula.TwistedOrbital
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Stabilizer cosets and locally closed twisted orbits -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.QuotientIntegration
open MeasureTheory Topology

variable {G : Type*} [Group G] [TopologicalSpace G] (θ : G ≃ₜ* G) (r : G)

/-- The actual twisted orbit, with the subspace topology of the ambient group. -/
abbrev TwistedOrbit := Set.range (fun x : G => twistedConj θ x r)

private def orbitPoint (x : G) : TwistedOrbit θ r := ⟨twistedConj θ x r, ⟨x, rfl⟩⟩

private theorem orbitPoint_eq_iff (x y : G) :
    orbitPoint θ r x = orbitPoint θ r y ↔ QuotientGroup.rightRel (twistedCentralizer θ r) x y := by
  rw [Subtype.ext_iff, QuotientGroup.rightRel_apply, mem_twistedCentralizer]
  change twistedConj θ x r = twistedConj θ y r ↔ twistedConj θ (y * x⁻¹) r = r
  constructor
  · intro h
    rw [← twistedConj_mul, ← h, twistedConj_mul, mul_inv_cancel, twistedConj_one]
  · intro h
    simpa only [twistedConj_mul, inv_mul_cancel_right] using
      congrArg (twistedConj θ x) h.symm

private def quotientOrbitPoint : LeftQuotient (twistedCentralizer θ r) → TwistedOrbit θ r :=
  Quotient.lift (orbitPoint θ r) (fun x y h => (orbitPoint_eq_iff θ r x y).2 h)

private theorem quotientOrbitPoint_bijective : Function.Bijective (quotientOrbitPoint θ r) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        intro h
        exact Quotient.sound ((orbitPoint_eq_iff θ r x y).1 h)
  · rintro ⟨y, x, rfl⟩
    exact ⟨Quotient.mk _ x, rfl⟩

variable [IsTopologicalGroup G]

private theorem continuous_orbitPoint : Continuous (orbitPoint θ r) :=
  ((continuous_inv.mul continuous_const).mul θ.continuous).subtype_mk _

private theorem isOpenMap_orbitPoint [SigmaCompactSpace G] [LocallyCompactSpace G] [T2Space G]
    (h : IsLocallyClosed (TwistedOrbit θ r)) : IsOpenMap (orbitPoint θ r) := by
  let act (a : G) (y : TwistedOrbit θ r) : TwistedOrbit θ r :=
    ⟨twistedConj θ a⁻¹ y, by
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x * a⁻¹, by rw [← hx, twistedConj_mul]⟩⟩
  let : MulAction G (TwistedOrbit θ r) :=
    { smul := act
      one_smul := fun x => Subtype.ext (by
        change twistedConj θ (1 : G)⁻¹ x = x.val
        rw [inv_one, twistedConj_one])
      mul_smul := fun a b x => Subtype.ext (by
        change twistedConj θ (a * b)⁻¹ x = twistedConj θ a⁻¹ (twistedConj θ b⁻¹ x)
        rw [mul_inv_rev, twistedConj_mul]) }
  let : ContinuousSMul G (TwistedOrbit θ r) :=
    ⟨(((continuous_fst.inv.inv.mul (continuous_subtype_val.comp continuous_snd)).mul
      (θ.continuous.comp continuous_fst.inv))).subtype_mk _⟩
  let : MulAction.IsPretransitive G (TwistedOrbit θ r) := ⟨by
    rintro ⟨x, u, rfl⟩ ⟨y, v, rfl⟩
    refine ⟨v⁻¹ * u, Subtype.ext ?_⟩
    change twistedConj θ (v⁻¹ * u)⁻¹ (twistedConj θ u r) = twistedConj θ v r
    rw [twistedConj_mul, mul_inv_rev, inv_inv, mul_inv_cancel_left]⟩
  let : LocallyCompactSpace (TwistedOrbit θ r) := h.locallyCompactSpace
  have hopen := (isOpenMap_smul_of_sigmaCompact (orbitPoint θ r 1)).comp (isOpenMap_inv G)
  convert hopen using 1
  funext x
  apply Subtype.ext
  change twistedConj θ x r = twistedConj θ x⁻¹⁻¹ (twistedConj θ 1 r)
  rw [inv_inv, twistedConj_one]

/-- Stabilizer cosets with their quotient topology identify with a locally closed
    twisted orbit in a sigma-compact locally compact Hausdorff group. -/
def twistedOrbitHomeomorph [SigmaCompactSpace G] [LocallyCompactSpace G] [T2Space G]
    (h : IsLocallyClosed (TwistedOrbit θ r)) :
    LeftQuotient (twistedCentralizer θ r) ≃ₜ TwistedOrbit θ r :=
  (Equiv.ofBijective _ (quotientOrbitPoint_bijective θ r)).toHomeomorphOfContinuousOpen
    (continuous_quot_lift _ (continuous_orbitPoint θ r)) (by
      intro U hU
      have hq := (leftQuotient_isOpenQuotientMap (twistedCentralizer θ r)).surjective
      have hopen := isOpenMap_orbitPoint θ r h _
        (hU.preimage continuous_quotient_mk')
      change IsOpen (quotientOrbitPoint θ r '' U)
      rw [← Set.image_preimage_eq U hq, ← Set.image_comp]
      exact hopen)

@[simp] theorem twistedOrbitHomeomorph_mk [SigmaCompactSpace G] [LocallyCompactSpace G] [T2Space G]
    (h : IsLocallyClosed (TwistedOrbit θ r)) (x : G) :
    (twistedOrbitHomeomorph θ r h (Quotient.mk _ x) : G) = twistedConj θ x r := rfl

/-- A closed twisted orbit gives integrability against any quotient measure finite on compacts. -/
theorem twistedOrbitFunction_integrable_of_isClosed [SigmaCompactSpace G] [LocallyCompactSpace G]
    [T2Space G] (h : IsClosed (TwistedOrbit θ r))
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ r))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ r))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ r))) [IsFiniteMeasureOnCompacts ν]
    (φ : G → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (twistedOrbitFunction θ r φ) ν := by
  let e := twistedOrbitHomeomorph θ r h.isLocallyClosed
  have heq : twistedOrbitFunction θ r φ = φ ∘ Subtype.val ∘ e := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => rfl
  rw [heq]
  exact (hφ.comp (continuous_subtype_val.comp e.continuous)).integrable_of_hasCompactSupport
    ((hc.comp_isClosedEmbedding h.isClosedEmbedding_subtypeVal).comp_homeomorph e)

end Langlands.TraceFormula
