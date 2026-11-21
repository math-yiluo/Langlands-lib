import Langlands.BaseChange.RegularTransferStatement
import Langlands.BaseChange.NormNeighbourhood
import Langlands.BaseChange.OrbitalIntegralPositivity
import Langlands.Representation.Hecke.TestFunction
import Langlands.Group.GL.LocalFieldTopology

/-! # A regular concordant pair detecting a prescribed norm -/

noncomputable section

open MeasureTheory Topology
open scoped ComplexOrder

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis Langlands.JacquetLanglands
open Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- With regular transfer, each regular semisimple norm has a concordant
test pair with nonzero ordinary orbital integral in every compatible
normalization and with ordinary support in any prescribed neighborhood. -/
def RegularConcordanceCalibrationStatement : Prop :=
  RegularTransferStatement.{u, v} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    letI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (γ : GeneralLinear n F), IsRegularSemisimple γ → IsNorm σ l γ →
      ∀ U ∈ nhds γ,
        ∃ (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
          IsSigmaRegularSupported σ l φ ∧ IsRegularSupported f ∧
          tsupport (f : GeneralLinear n F → ℂ) ⊆ U ∧ f γ = 1 ∧
          AreConcordant σ l μF μE φ f ∧
          ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
            (νγ : Measure (LeftQuotient (glCentralizer γ))),
            IsCompatible (glCentralizer γ) μF μγ νγ → 0 < orbitalIntegral γ νγ f

set_option maxHeartbeats 700000 in
theorem regularConcordanceCalibration : RegularConcordanceCalibrationStatement.{u, v} := by
  unfold RegularConcordanceCalibrationStatement
  intro hTransfer F _ _ _ _ _ E _ _ _ _ _ σ l n hσ μF hμF μE _ γ hReg hNorm U hU
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : NonarchimedeanGroup (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_nonarchimedean F n
  let S : Set (GeneralLinear n F) := {x | IsRegularSemisimple x ∧ IsNorm σ l x}
  have hS : IsOpen S := ((normNeighbourhood F n).2 E σ l hσ).2
  let L := Homeomorph.mulLeft γ
  have hγS : γ ∈ S := ⟨hReg, hNorm⟩
  have hN : U ∩ S ∈ nhds (L 1) := by
    change U ∩ S ∈ nhds (γ * 1)
    rw [mul_one]
    exact Filter.inter_mem hU (hS.mem_nhds hγS)
  obtain ⟨J, hJc, hJ⟩ := compactOpenSubgroupBasis (GeneralLinear n F)
    (L ⁻¹' (U ∩ S)) (L.continuous.continuousAt.preimage_mem_nhds hN)
  let W := L '' (J : Set (GeneralLinear n F))
  have hWc : IsCompact W := hJc.image L.continuous
  have hWo : IsOpen W := L.isOpenMap _ J.isOpen
  have hW : W ⊆ U ∩ S := Set.image_subset_iff.mpr hJ
  have hγW : γ ∈ W := ⟨1, J.one_mem, mul_one γ⟩
  have hWcl : IsClopen W := ⟨hWc.isClosed, hWo⟩
  let f := Hecke.TestFunction.characteristic hWcl hWc
  have hSupport : Function.support (f : GeneralLinear n F → ℂ) = W :=
    Hecke.TestFunction.support_characteristic hWcl hWc
  have hfγ : f γ = 1 := Set.indicator_of_mem hγW _
  have hfreg : IsRegularSupported f := by
    intro x hx
    have hxW : x ∈ W := hSupport ▸ hx
    exact (hW hxW).2.1
  have hfvan : VanishesOffNorms σ l μF f := by
    intro y _ hy μy _ _ νy _
    suffices hzero : twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) y
        (f : GeneralLinear n F → ℂ) = 0 by
      simp only [orbitalIntegral, twistedOrbitalIntegral, hzero, Pi.zero_apply, integral_zero]
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [twistedOrbitFunction_mk, MonoidHom.id_apply, Pi.zero_apply]
      by_contra hx
      have hxW : x⁻¹ * y * x ∈ W := hSupport ▸ hx
      obtain ⟨δ, hδ⟩ := (hW hxW).2.2
      exact hy ⟨_, by simpa [mul_assoc] using hδ.twistedConj hσ.pow_eq_one 1 x⁻¹⟩
  obtain ⟨φ, hφ, hMatch⟩ := (hTransfer F E σ l n hσ μF μE).2 f hfreg hfvan
  refine ⟨φ, f, hφ, hfreg, ?_, hfγ, hMatch, ?_⟩
  · change closure (Function.support (f : GeneralLinear n F → ℂ)) ⊆ U
    rw [hSupport, hWcl.isClosed.closure_eq]
    exact fun x hx => (hW hx).1
  · intro μγ _ _ νγ hν
    refine orbitalIntegralPositivity F n μF hμF f γ hReg ?_ (by rw [hfγ]; exact zero_lt_one) μγ νγ hν
    intro x
    by_cases hx : x ∈ W
    · change 0 ≤ W.indicator (fun _ => (1 : ℂ)) x
      rw [Set.indicator_of_mem hx]
      exact zero_le_one
    · change 0 ≤ W.indicator (fun _ => (1 : ℂ)) x
      rw [Set.indicator_of_notMem hx]

end Langlands.BaseChange
