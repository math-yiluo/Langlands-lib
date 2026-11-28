import Langlands.TraceFormula.SingleOrbitGeometricTrace

/-!
# Matching the terms of a twisted and an ordinary finite geometric expansion

Two finite geometric expansions are compared through a relation `A` between rational
points of the two groups. The relation is invariant under rational (twisted) conjugation
on both sides, determines classes uniquely in both directions, and every regular
twisted point is related to some ordinary point. Related terms match after transport of
the measures and a scalar `c`. Ordinary terms at regular points with no related twisted
point vanish. The twisted expansion then equals `c` times the ordinary one.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration Langlands.BaseChange

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Pairing

variable {GW GG : Type*}
  [Group GW] [TopologicalSpace GW] [IsTopologicalGroup GW] [MeasurableSpace GW] [BorelSpace GW]
  [Group GG] [TopologicalSpace GG] [IsTopologicalGroup GG] [MeasurableSpace GG] [BorelSpace GG]

/-- Matching of a twisted geometric term with an ordinary one, from the twisted side: every
choice of measures for the `θ`-twisted term at `x` has a choice of measures for the ordinary
term at `y` with the same rational covolume, and the twisted orbital integral of `φ` at `x` is
`c` times the orbital integral of `f` at `y`. -/
def TwistedTermMatchesOrdinaryTerm (RW : Subgroup GW) (RG : Subgroup GG) (θ : GW →* GW)
    (μW : Measure GW) (μG : Measure GG) (φ : GW → ℂ) (f : GG → ℂ) (c : ℂ) (x : GW) (y : GG) :
    Prop :=
  ∀ d : TwistedGeometricMeasures RW θ x μW,
    ∃ d' : TwistedGeometricMeasures RG (MonoidHom.id GG) y μG,
      d.rational Set.univ = d'.rational Set.univ ∧
      twistedOrbitalIntegral θ x d.orbital φ = c * orbitalIntegral y d'.orbital f

/-- Matching of an ordinary geometric term with a twisted one, from the ordinary side: every
choice of measures for the ordinary term at `y` has a choice of measures for the `θ`-twisted
term at `x` for which the twisted orbital integral of `φ` at `x` is `c` times the orbital
integral of `f` at `y`. -/
def OrdinaryTermMatchesTwistedTerm (RW : Subgroup GW) (RG : Subgroup GG) (θ : GW →* GW)
    (μW : Measure GW) (μG : Measure GG) (φ : GW → ℂ) (f : GG → ℂ) (c : ℂ) (x : GW) (y : GG) :
    Prop :=
  ∀ d' : TwistedGeometricMeasures RG (MonoidHom.id GG) y μG,
    ∃ d : TwistedGeometricMeasures RW θ x μW,
      twistedOrbitalIntegral θ x d.orbital φ = c * orbitalIntegral y d'.orbital f

/-- Term-by-term comparison of a twisted and an ordinary finite geometric expansion.

The twisted expansion `T` runs over pairwise non-`θ`-conjugate rational points `r j`
covering the twisted support of `φ`; the ordinary expansion `U` runs over pairwise
non-conjugate rational points `q k` covering the support of `f`. Both hold for every
choice of the measures in the terms. The relation `A` between rational points is
invariant under rational conjugation on each side and determines classes uniquely in
both directions. Each regular `r` has a related ordinary point. Related terms match up
to `c`, in either direction of measure transport, when one of the two points is regular.
Ordinary orbital integrals at regular points related to no rational point vanish. Then
`T = c * U`. -/
theorem geometricExpansion_eq_mul_of_termPairing
    (RW : Subgroup GW) (RG : Subgroup GG) (θ : GW →* GW) (μW : Measure GW) (μG : Measure GG)
    (φ : GW → ℂ) (f : GG → ℂ) (c T U : ℂ)
    (A : RW → RG → Prop) (regW : RW → Prop) (regG : RG → Prop)
    {m m' : ℕ} (r : Fin m → RW) (q : Fin m' → RG)
    (hT : ∀ d : ∀ j, TwistedGeometricMeasures RW θ (r j : GW) μW, T = ∑ j, (d j).term φ)
    (hU : ∀ d : ∀ k, TwistedGeometricMeasures RG (MonoidHom.id GG) (q k : GG) μG,
      U = ∑ k, (d k).term f)
    (hrD : ∀ j j', IsTwistedConjugate RW θ (r j : GW) (r j' : GW) → j = j')
    (hqD : ∀ k k', IsTwistedConjugate RG (MonoidHom.id GG) (q k : GG) (q k' : GG) → k = k')
    (hrC : ∀ x : RW, (∃ g : GW, φ (g⁻¹ * (x : GW) * θ g) ≠ 0) →
      ∃ j, IsTwistedConjugate RW θ (r j : GW) (x : GW))
    (hqC : ∀ y : RG, (∃ g : GG, f (g⁻¹ * (y : GG) * g) ≠ 0) →
      ∃ k, IsTwistedConjugate RG (MonoidHom.id GG) (q k : GG) (y : GG))
    (hrReg : ∀ j, regW (r j)) (hqReg : ∀ k, regG (q k))
    (hrM : ∀ j, Nonempty (TwistedGeometricMeasures RW θ (r j : GW) μW))
    (hqM : ∀ k, Nonempty (TwistedGeometricMeasures RG (MonoidHom.id GG) (q k : GG) μG))
    (hNorm : ∀ x : RW, regW x → ∃ y : RG, A x y)
    (hAW : ∀ (x x' : RW) (y : RG), A x y → IsTwistedConjugate RW θ (x : GW) (x' : GW) → A x' y)
    (hAG : ∀ (x : RW) (y y' : RG), A x y →
      IsTwistedConjugate RG (MonoidHom.id GG) (y : GG) (y' : GG) → A x y')
    (hUW : ∀ (x x' : RW) (y : RG), A x y → A x' y →
      IsTwistedConjugate RW θ (x : GW) (x' : GW))
    (hUG : ∀ (x : RW) (y y' : RG), A x y → A x y' →
      IsTwistedConjugate RG (MonoidHom.id GG) (y : GG) (y' : GG))
    (hMatchW : ∀ (x : RW) (y : RG), A x y → regW x ∨ regG y →
      TwistedTermMatchesOrdinaryTerm RW RG θ μW μG φ f c (x : GW) (y : GG))
    (hMatchG : ∀ (x : RW) (y : RG), A x y → regW x ∨ regG y →
      OrdinaryTermMatchesTwistedTerm RW RG θ μW μG φ f c (x : GW) (y : GG))
    (hOff : ∀ y : RG, regG y → (∀ x : RW, ¬ A x y) →
      ∀ d' : TwistedGeometricMeasures RG (MonoidHom.id GG) (y : GG) μG,
        orbitalIntegral (y : GG) d'.orbital f = 0) :
    T = c * U := by
  classical
  let P : Fin m → Fin m' → Prop := fun j k => A (r j) (q k)
  have hPk (j : Fin m) (k k' : Fin m') (h : P j k) (h' : P j k') : k = k' :=
    hqD k k' (hUG (r j) (q k) (q k') h h')
  have hPj (j j' : Fin m) (k : Fin m') (h : P j k) (h' : P j' k) : j = j' :=
    hrD j j' (hUW (r j) (r j') (q k) h h')
  let d : ∀ j, TwistedGeometricMeasures RW θ (r j : GW) μW := fun j => (hrM j).some
  have hChosen (k : Fin m') : ∃ d' : TwistedGeometricMeasures RG (MonoidHom.id GG) (q k : GG) μG,
      ∀ j, P j k → (d j).rational Set.univ = d'.rational Set.univ ∧
        twistedOrbitalIntegral θ (r j : GW) (d j).orbital φ =
          c * orbitalIntegral (q k : GG) d'.orbital f := by
    by_cases h : ∃ j, P j k
    · obtain ⟨j, hj⟩ := h
      obtain ⟨d', hvol, hint⟩ := hMatchW (r j) (q k) hj (Or.inl (hrReg j)) (d j)
      refine ⟨d', fun j' hj' => ?_⟩
      obtain rfl := hPj j j' k hj hj'
      exact ⟨hvol, hint⟩
    · exact ⟨(hqM k).some, fun j hj => (h ⟨j, hj⟩).elim⟩
  choose d' hd' using hChosen
  have hRow (j : Fin m) :
      (d j).term φ = ∑ k, if P j k then (d j).term φ else 0 := by
    by_cases ha : (d j).term φ = 0
    · simp only [ha, ite_self, Finset.sum_const_zero]
    · have hO : twistedOrbitalIntegral θ (r j : GW) (d j).orbital φ ≠ 0 := by
        intro h0
        apply ha
        simp only [TwistedGeometricMeasures.term, h0, mul_zero]
      obtain ⟨y, hy⟩ := hNorm (r j) (hrReg j)
      obtain ⟨e, -, he⟩ := hMatchW (r j) y hy (Or.inl (hrReg j)) (d j)
      have hO' : orbitalIntegral (y : GG) e.orbital f ≠ 0 := by
        intro h0
        apply hO
        rw [he, h0, mul_zero]
      obtain ⟨g, hg⟩ := exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero _ f hO'
      obtain ⟨k, hk⟩ := hqC y ⟨g, hg⟩
      have hjk : P j k := hAG (r j) y (q k) hy hk.symm
      rw [Finset.sum_eq_single k]
      · rw [ite_eq_left hjk]
      · intro k' _ hk'
        refine ite_eq_right fun h => ?_
        exact hk' (hPk j k' k h hjk)
      · simp
  have hColumn (k : Fin m') :
      c * (d' k).term f = ∑ j, if P j k then (d j).term φ else 0 := by
    by_cases h : ∃ j, P j k
    · obtain ⟨j, hj⟩ := h
      rw [Finset.sum_eq_single j]
      · rw [ite_eq_left hj]
        simp only [TwistedGeometricMeasures.term, (hd' k j hj).1, (hd' k j hj).2]
        ring
      · intro j' _ hj'
        refine ite_eq_right fun h' => ?_
        exact hj' (hPj j' j k h' hj)
      · simp
    · rw [Finset.sum_eq_zero (fun j _ => ite_eq_right fun hj => h ⟨j, hj⟩)]
      by_contra hne
      have hc : c ≠ 0 := by
        intro h0
        apply hne
        rw [h0, zero_mul]
      have hO : orbitalIntegral (q k : GG) (d' k).orbital f ≠ 0 := by
        intro h0
        apply hne
        simp only [TwistedGeometricMeasures.term, orbitalIntegral] at h0 ⊢
        rw [h0, mul_zero, mul_zero]
      by_cases hex : ∃ x : RW, A x (q k)
      · obtain ⟨x, hx⟩ := hex
        obtain ⟨e, he⟩ := hMatchG x (q k) hx (Or.inr (hqReg k)) (d' k)
        have hO' : twistedOrbitalIntegral θ (x : GW) e.orbital φ ≠ 0 := by
          rw [he]
          exact mul_ne_zero hc hO
        obtain ⟨g, hg⟩ := exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero _ φ hO'
        obtain ⟨j, hj⟩ := hrC x ⟨g, hg⟩
        exact h ⟨j, hAW x (r j) (q k) hx hj.symm⟩
      · exact hO (hOff (q k) (hqReg k) (fun x hx => hex ⟨x, hx⟩) (d' k))
  rw [hT d, hU d', Finset.mul_sum]
  calc ∑ j, (d j).term φ = ∑ j, ∑ k, (if P j k then (d j).term φ else 0) :=
        Finset.sum_congr rfl fun j _ => hRow j
    _ = ∑ k, ∑ j, (if P j k then (d j).term φ else 0) := Finset.sum_comm
    _ = ∑ k, c * (d' k).term f := Finset.sum_congr rfl fun k _ => (hColumn k).symm

/-- The term pairing of `geometricExpansion_eq_mul_of_termPairing` for the monoid
homomorphism underlying a topological group automorphism `θ`, with the distinctness and
covering hypotheses on both sides stated in the form of the simple (twisted) trace formula. -/
theorem geometricExpansion_eq_mul_of_termPairing_continuousMulEquiv
    (RW : Subgroup GW) (RG : Subgroup GG) (θ : GW ≃ₜ* GW) (μW : Measure GW) (μG : Measure GG)
    (φ : GW → ℂ) (f : GG → ℂ) (c T U : ℂ)
    (A : RW → RG → Prop) (regW : RW → Prop) (regG : RG → Prop)
    {m m' : ℕ} (r : Fin m → RW) (q : Fin m' → RG)
    (hT : ∀ d : ∀ j, TwistedGeometricMeasures RW θ.toMonoidHom (r j : GW) μW,
      T = ∑ j, (d j).term φ)
    (hU : ∀ d : ∀ k, TwistedGeometricMeasures RG (MonoidHom.id GG) (q k : GG) μG,
      U = ∑ k, (d k).term f)
    (hrD : ∀ j j', IsTwistedConjugate RW θ (r j : GW) (r j' : GW) → j = j')
    (hqD : ∀ k k', IsTwistedConjugate RG (MonoidHom.id GG) (q k : GG) (q k' : GG) → k = k')
    (hrC : ∀ x ∈ RW, (∃ g : GW, φ (g⁻¹ * x * θ g) ≠ 0) →
      ∃ j, IsTwistedConjugate RW θ (r j : GW) x)
    (hqC : ∀ y ∈ RG, (∃ g : GG, f (g⁻¹ * y * g) ≠ 0) →
      ∃ k, IsTwistedConjugate RG (MonoidHom.id GG) (q k : GG) y)
    (hrReg : ∀ j, regW (r j)) (hqReg : ∀ k, regG (q k))
    (hrM : ∀ j, Nonempty (TwistedGeometricMeasures RW θ.toMonoidHom (r j : GW) μW))
    (hqM : ∀ k, Nonempty (TwistedGeometricMeasures RG (MonoidHom.id GG) (q k : GG) μG))
    (hNorm : ∀ x : RW, regW x → ∃ y : RG, A x y)
    (hAW : ∀ (x x' : RW) (y : RG), A x y →
      IsTwistedConjugate RW θ.toMonoidHom (x : GW) (x' : GW) → A x' y)
    (hAG : ∀ (x : RW) (y y' : RG), A x y →
      IsTwistedConjugate RG (MonoidHom.id GG) (y : GG) (y' : GG) → A x y')
    (hUW : ∀ (x x' : RW) (y : RG), A x y → A x' y →
      IsTwistedConjugate RW θ.toMonoidHom (x : GW) (x' : GW))
    (hUG : ∀ (x : RW) (y y' : RG), A x y → A x y' →
      IsTwistedConjugate RG (MonoidHom.id GG) (y : GG) (y' : GG))
    (hMatchW : ∀ (x : RW) (y : RG), A x y → regW x ∨ regG y →
      TwistedTermMatchesOrdinaryTerm RW RG θ.toMonoidHom μW μG φ f c (x : GW) (y : GG))
    (hMatchG : ∀ (x : RW) (y : RG), A x y → regW x ∨ regG y →
      OrdinaryTermMatchesTwistedTerm RW RG θ.toMonoidHom μW μG φ f c (x : GW) (y : GG))
    (hOff : ∀ y : RG, regG y → (∀ x : RW, ¬ A x y) →
      ∀ d' : TwistedGeometricMeasures RG (MonoidHom.id GG) (y : GG) μG,
        orbitalIntegral (y : GG) d'.orbital f = 0) :
    T = c * U :=
  geometricExpansion_eq_mul_of_termPairing RW RG θ.toMonoidHom μW μG φ f c T U A regW regG r q
    hT hU hrD hqD (fun x hx => hrC x x.2 hx) (fun y hy => hqC y y.2 hy) hrReg hqReg hrM hqM
    hNorm hAW hAG hUW hUG hMatchW hMatchG hOff

end Pairing

section Transport

variable {G₁ G₂ : Type*}
  [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [MeasurableSpace G₂] [BorelSpace G₂]

private theorem map_count_eq_count {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) : Measure.map e (Measure.count : Measure X) = Measure.count := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, Measure.count_apply (e.measurable hs),
    Measure.count_apply hs, Set.encard_preimage_of_bijective e.bijective]

/-- Transport of the measures in one geometric term along a continuous isomorphism of
twisted centralizers that matches the rational points. The centralizer measure is pushed
forward, the rational covolume is unchanged, and the orbital quotient measure is any
compatible one for the target. The target centralizer is commutative, so the pushed
measure is a Haar measure. -/
theorem exists_twistedGeometricMeasures_map [T2Space G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂]
    {Γ₁ : Subgroup G₁} {θ₁ : G₁ →* G₁} {δ₁ : G₁} {μ₁ : Measure G₁}
    {Γ₂ : Subgroup G₂} {θ₂ : G₂ →* G₂} {δ₂ : G₂} (μ₂ : Measure G₂)
    [μ₂.IsHaarMeasure] [μ₂.IsMulRightInvariant] (hθ₂ : Continuous θ₂)
    (e : twistedCentralizer θ₁ δ₁ ≃ₜ* twistedCentralizer θ₂ δ₂)
    (he : ∀ x : twistedCentralizer θ₁ δ₁, (e x : G₂) ∈ Γ₂ ↔ (x : G₁) ∈ Γ₁)
    (hcomm : ∀ x y : twistedCentralizer θ₂ δ₂, x * y = y * x)
    (d : TwistedGeometricMeasures Γ₁ θ₁ δ₁ μ₁) :
    ∃ d' : TwistedGeometricMeasures Γ₂ θ₂ δ₂ μ₂,
      d'.centralizer = d.centralizer.map e ∧ d'.rational Set.univ = d.rational Set.univ := by
  let C₁ := twistedCentralizer θ₁ δ₁
  let C₂ := twistedCentralizer θ₂ δ₂
  let R₁ := Γ₁.subgroupOf C₁
  let R₂ := Γ₂.subgroupOf C₂
  have hC : IsClosed (C₂ : Set G₂) := isClosed_twistedCentralizer θ₂ hθ₂ δ₂
  let : LocallyCompactSpace C₂ := hC.locallyCompactSpace
  let : SecondCountableTopology C₂ :=
    TopologicalSpace.Subtype.secondCountableTopology (C₂ : Set G₂)
  let := d.rightInvariant
  let := d.finiteOnCompacts
  let := d.openPos
  let μC : Measure C₂ := d.centralizer.map e
  let hR : μC.IsMulRightInvariant := isMulRightInvariant_map e d.centralizer
  have hFin : IsFiniteMeasureOnCompacts μC :=
    Measure.IsFiniteMeasureOnCompacts.map d.centralizer e.toHomeomorph
  have hPos : μC.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hL : μC.IsMulLeftInvariant := ⟨fun g => by
    have h : (fun y : C₂ => g * y) = fun y => y * g := funext fun y => hcomm g y
    rw [h, map_mul_right_eq_self]⟩
  have hHaar : μC.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hFin, toIsMulLeftInvariant := hL,
      toIsOpenPosMeasure := hPos }
  have hReg : μC.Regular := inferInstance
  obtain ⟨ν, hν⟩ := compatibleMeasureExists C₂ hC μ₂ μC
  have hmem (x : C₁) : e x ∈ R₂ ↔ x ∈ R₁ := by
    simp only [R₁, R₂, Subgroup.mem_subgroupOf]
    exact he x
  let eΓ : R₁ ≃ₜ* R₂ := subgroupContinuousMulEquiv e R₁ R₂ hmem
  let eΓQ : LeftQuotient R₁ ≃ₜ LeftQuotient R₂ :=
    Homeomorph.Quotient.congr e.toHomeomorph (by
      intro y z
      rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
      change z * y⁻¹ ∈ R₁ ↔ e z * (e y)⁻¹ ∈ R₂
      rw [← map_inv, ← map_mul]
      exact (hmem _).symm)
  have hνΓ : IsCompatible R₂ μC Measure.count (Measure.map eΓQ d.rational) := by
    have hmap := isCompatible_map_equiv e R₁ R₂ eΓ (fun _ => rfl) eΓQ (fun _ => rfl)
      d.centralizer Measure.count d.rational d.rational_compatible
    have hcount : Measure.map eΓ (Measure.count : Measure R₁) = Measure.count :=
      map_count_eq_count eΓ.toHomeomorph.toMeasurableEquiv
    simpa only [hcount] using hmap
  refine ⟨⟨μC, hR, hFin, hPos, ν, Measure.map eΓQ d.rational, hν, hνΓ⟩, rfl, ?_⟩
  change Measure.map eΓQ d.rational Set.univ = d.rational Set.univ
  rw [Measure.map_apply eΓQ.continuous.measurable MeasurableSet.univ, Set.preimage_univ]

end Transport

end Langlands.TraceFormula
