import Langlands.TraceFormula.TwistedGeometricConjugation
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.Analysis.Local.QuotientMeasureExistence

/-! # Reducing a finite geometric trace expansion to one rational class -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Topology
open Langlands.QuotientIntegration Langlands.BaseChange

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

open scoped ENNReal

variable {G : Type*} [Group G]

theorem IsTwistedConjugate.symm {Γ : Subgroup G} {θ : G →* G} {x y : G}
    (h : IsTwistedConjugate Γ θ x y) : IsTwistedConjugate Γ θ y x := by
  obtain ⟨g, hg, he⟩ := h
  refine ⟨g⁻¹, Γ.inv_mem hg, ?_⟩
  change twistedConj θ g x = y at he
  change twistedConj θ g⁻¹ y = x
  rw [← he, twistedConj_mul, mul_inv_cancel, twistedConj_one]

theorem IsTwistedConjugate.trans {Γ : Subgroup G} {θ : G →* G} {x y z : G}
    (h₁ : IsTwistedConjugate Γ θ x y) (h₂ : IsTwistedConjugate Γ θ y z) :
    IsTwistedConjugate Γ θ x z := by
  obtain ⟨g, hg, hgy⟩ := h₁
  obtain ⟨k, hk, hkz⟩ := h₂
  refine ⟨g * k, Γ.mul_mem hg hk, ?_⟩
  change twistedConj θ g x = y at hgy
  change twistedConj θ k y = z at hkz
  change twistedConj θ (g * k) x = z
  rw [← twistedConj_mul, hgy, hkz]

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The two compatible quotients and their shared centralizer measure in one
geometric trace term. The subgroup measure on the rational intersection is counting. -/
structure TwistedGeometricMeasures (Γ : Subgroup G) (θ : G →* G) (δ : G) (μG : Measure G) where
  centralizer : Measure (twistedCentralizer θ δ)
  rightInvariant : centralizer.IsMulRightInvariant
  finiteOnCompacts : IsFiniteMeasureOnCompacts centralizer
  openPos : centralizer.IsOpenPosMeasure
  orbital : Measure (LeftQuotient (twistedCentralizer θ δ))
  rational : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ δ)))
  orbital_compatible :
    letI := rightInvariant
    IsCompatible (twistedCentralizer θ δ) μG centralizer orbital
  rational_compatible :
    IsCompatible (Γ.subgroupOf (twistedCentralizer θ δ)) centralizer Measure.count rational

variable {Γ : Subgroup G} {θ : G →* G} {δ : G} {μG : Measure G}

/-- The centralizer covolume times the twisted orbital integral in the simple trace formula. -/
def TwistedGeometricMeasures.term (d : TwistedGeometricMeasures Γ θ δ μG) (f : G → ℂ) : ℂ :=
  ((d.rational Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ δ d.orbital f

/-- For a commutative twisted centralizer and discrete rational subgroup, both
compatible measures exist. The ambient measure is the supplied two-sided Haar. -/
theorem nonempty_twistedGeometricMeasures_of_commutative [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (hΓ : IsDiscrete (Γ : Set G)) (hθ : Continuous θ)
    (hcomm : ∀ x y : twistedCentralizer θ δ, x * y = y * x) :
    Nonempty (TwistedGeometricMeasures Γ θ δ μG) := by
  let C := twistedCentralizer θ δ
  let R := Γ.subgroupOf C
  have hC : IsClosed (C : Set G) := isClosed_twistedCentralizer θ hθ δ
  have hR : IsDiscrete (R : Set C) :=
    hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  have hRclosed : IsClosed (R : Set C) := R.isClosed_of_isDiscrete hR
  let : DiscreteTopology R := SetLike.isDiscrete_iff_discreteTopology.mp hR
  let : BorelSpace C := Subtype.borelSpace (· ∈ C)
  let : BorelSpace R := Subtype.borelSpace (· ∈ R)
  let : LocallyCompactSpace C := hC.locallyCompactSpace
  let : SecondCountableTopology C := TopologicalSpace.Subtype.secondCountableTopology (C : Set G)
  let : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set C)
  let μC : Measure C := Measure.haar
  let hRight : μC.IsMulRightInvariant := ⟨fun x => by
    have he : (fun y : C => y * x) = fun y => x * y := funext fun y => hcomm y x
    rw [he, map_mul_left_eq_self]⟩
  let : (Measure.count : Measure R).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete
      toIsMulLeftInvariant := inferInstance
      open_pos := fun _ _ hU => Measure.count_ne_zero hU }
  obtain ⟨ν, hν⟩ := compatibleMeasureExists C hC μG μC
  obtain ⟨νΓ, hνΓ⟩ := compatibleMeasureExists R hRclosed μC Measure.count
  exact ⟨⟨μC, hRight, inferInstance, inferInstance, ν, νΓ, hν, hνΓ⟩⟩

private theorem exists_conjugate_geometricMeasures [μG.IsMulLeftInvariant]
    {r : G} (hr : IsTwistedConjugate Γ θ δ r) (d : TwistedGeometricMeasures Γ θ δ μG) :
    ∃ e : TwistedGeometricMeasures Γ θ r μG,
      e.rational Set.univ = d.rational Set.univ ∧
      ∀ f : G → ℂ, twistedOrbitalIntegral θ r e.orbital f =
        twistedOrbitalIntegral θ δ d.orbital f := by
  obtain ⟨x, hx, hxr⟩ := hr
  change twistedConj θ x δ = r at hxr
  subst r
  let := d.rightInvariant
  let := d.finiteOnCompacts
  let := d.openPos
  obtain ⟨μ, ν, νΓ, hFin, hPos, hR, hν, hνΓ, hvol, hint⟩ :=
    twistedGeometricConjugation Γ θ δ x hx μG d.centralizer d.orbital d.rational
      d.orbital_compatible d.rational_compatible
  exact ⟨⟨μ, hR, hFin, hPos, ν, νΓ, hν, hνΓ⟩, hvol, hint⟩

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
theorem exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G → ℂ)
    (hn : twistedOrbitalIntegral θ δ ν f ≠ 0) : ∃ x : G, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra! h
  apply hn
  have hz : twistedOrbitFunction θ δ f = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact h x
  simp only [twistedOrbitalIntegral, hz, Pi.zero_apply, integral_zero]

/-- A finite geometric trace expansion with one contributing rational class
equals its weighted orbital term with any supplied compatible measures. -/
def SingleOrbitGeometricTraceStatement [μG.IsMulLeftInvariant] (r₀ : Γ)
    (d₀ : TwistedGeometricMeasures Γ θ (r₀ : G) μG) (f : G → ℂ) (t : ℂ)
    {m : ℕ} (r : Fin m → Γ) : Prop :=
  (∀ j k, IsTwistedConjugate Γ θ (r j : G) (r k : G) → j = k) →
  (∀ q : Γ, (∃ x : G, f (x⁻¹ * (q : G) * θ x) ≠ 0) →
    ∃ j, IsTwistedConjugate Γ θ (r j : G) (q : G)) →
  (∀ q : Γ, (∃ x : G, f (x⁻¹ * (q : G) * θ x) ≠ 0) →
    IsTwistedConjugate Γ θ (q : G) (r₀ : G)) →
  (∀ j, Nonempty (TwistedGeometricMeasures Γ θ (r j : G) μG)) →
  (∀ d : ∀ j, TwistedGeometricMeasures Γ θ (r j : G) μG,
    (∀ j, (d j).rational Set.univ ≠ ⊤) ∧ t = ∑ j, (d j).term f) →
  (twistedOrbitalIntegral θ (r₀ : G) d₀.orbital f ≠ 0 → d₀.rational Set.univ ≠ ⊤) ∧
  t = d₀.term f

set_option maxHeartbeats 1100000 in
theorem singleOrbitGeometricTrace [μG.IsMulLeftInvariant] (r₀ : Γ)
    (d₀ : TwistedGeometricMeasures Γ θ (r₀ : G) μG) (f : G → ℂ) (t : ℂ)
    {m : ℕ} (r : Fin m → Γ) : SingleOrbitGeometricTraceStatement r₀ d₀ f t r := by
  classical
  intro hDistinct hCover hIsolate hMeasures hTrace
  let O₀ := twistedOrbitalIntegral θ (r₀ : G) d₀.orbital f
  let P (j : Fin m) := IsTwistedConjugate Γ θ (r₀ : G) (r j : G)
  have hChosen (j : Fin m) : ∃ d : TwistedGeometricMeasures Γ θ (r j : G) μG,
      P j → d.rational Set.univ = d₀.rational Set.univ ∧
        twistedOrbitalIntegral θ (r j : G) d.orbital f = O₀ := by
    by_cases hj : P j
    · obtain ⟨d, hVol, hInt⟩ := exists_conjugate_geometricMeasures hj d₀
      exact ⟨d, fun _ => ⟨hVol, hInt f⟩⟩
    · exact ⟨(hMeasures j).some, fun h => (hj h).elim⟩
  choose d hd using hChosen
  obtain ⟨hFinite, ht⟩ := hTrace d
  have hZero (j : Fin m) (hj : ¬ P j) : (d j).term f = 0 := by
    have hO : twistedOrbitalIntegral θ (r j : G) (d j).orbital f = 0 := by
      by_contra hn
      exact hj (hIsolate (r j) (exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero _ f hn)).symm
    simp only [TwistedGeometricMeasures.term, hO, mul_zero]
  by_cases hO : O₀ = 0
  · have hAll (j : Fin m) : (d j).term f = 0 := by
      by_cases hj : P j
      · simp only [TwistedGeometricMeasures.term, (hd j hj).2, hO, mul_zero]
      · exact hZero j hj
    have hsum : t = 0 := by rw [ht]; simp only [hAll, Finset.sum_const_zero]
    exact ⟨fun hn => (hn hO).elim, by
      rw [hsum]
      change 0 = ((d₀.rational Set.univ).toReal : ℂ) * O₀
      rw [hO, mul_zero]⟩
  · obtain ⟨j, hj⟩ := hCover r₀ (exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero _ f hO)
    have hj' : P j := hj.symm
    have hterm : (d j).term f = d₀.term f := by
      simp only [TwistedGeometricMeasures.term, (hd j hj').1, (hd j hj').2, O₀]
    refine ⟨fun _ => ?_, ?_⟩
    · rw [← (hd j hj').1]
      exact hFinite j
    · rw [ht, Finset.sum_eq_single j, hterm]
      · intro k _ hk
        apply hZero k
        intro hk'
        exact hk (hDistinct k j (hk'.symm.trans hj'))
      · simp

end Langlands.TraceFormula
