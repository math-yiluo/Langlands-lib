import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.Representation.GodementJacquet.AnalyticData

/-! Actual rectangular Fourier integrals of entrywise affine lattice boxes. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uF

private theorem indicator_pi_one {ι X : Type*} [Fintype ι]
    (C : ι → Set X) (x : ι → X) :
    (Set.univ.pi C).indicator (fun _ => (1 : ℂ)) x =
      ∏ i, (C i).indicator (fun _ => (1 : ℂ)) (x i) := by
  simpa only [Finset.coe_univ, Pi.one_def] using
    (Set.indicator_pi_one_apply (M₀ := ℂ) Finset.univ C x)

private theorem character_sum {K ι : Type*} [AddCommGroup K] [TopologicalSpace K]
    (ψ : UnitaryAdditiveCharacter K) (S : Finset ι) (a : ι → K) :
    ψ.complex (∑ i ∈ S, a i) = ∏ i ∈ S, ψ.complex (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

section Tensor

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  [SigmaFinite μ.measure] {r s : ℕ}

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
private theorem entrywise_kernel (g : Fin r → Fin s → K → ℂ)
    (X Y : Matrix (Fin r) (Fin s) K) :
    (∏ i, ∏ j, g i j (X i j)) * ψ.complex (rectangularPairing X Y) =
      ∏ i, ∏ j, ψ.complex (X i j * Y i j) * g i j (X i j) := by
  rw [mul_comm, rectangularPairing, character_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [character_sum, ← Finset.prod_mul_distrib]

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalRing K] [BorelSpace K] in
private theorem entrywise_fourierIntegral (g : Fin r → Fin s → K → ℂ)
    (Y : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ μ (fun X => ∏ i, ∏ j, g i j (X i j)) Y =
      ∏ i, ∏ j, fourierIntegral ψ μ (g i j) (Y i j) := by
  unfold rectangularFourierIntegral RankinSelberg.rectangularMeasure
  simp_rw [entrywise_kernel]
  have hrow (i : Fin r) :
      (∫ x : Fin s → K, ∏ j,
        ψ.complex (x j * Y i j) * g i j (x j) ∂rowMeasure μ s) =
      ∏ j, fourierIntegral ψ μ (g i j) (Y i j) := by
    change (∫ x : Fin s → K, ∏ j,
        ψ.complex (x j * Y i j) * g i j (x j) ∂Measure.pi (fun _ : Fin s => μ.measure)) =
      ∏ j, ∫ x : K, ψ.complex (x * Y i j) * g i j x ∂μ.measure
    exact integral_fintype_prod_eq_prod
      (μ := fun _ : Fin s => μ.measure)
      (fun j x => ψ.complex (x * Y i j) * g i j x)
  have hout := integral_fintype_prod_eq_prod
    (E := fun _ : Fin r => Fin s → K)
    (μ := fun _ : Fin r => rowMeasure μ s)
    (fun i x => ∏ j, ψ.complex (x j * Y i j) * g i j (x j))
  exact hout.trans (Finset.prod_congr rfl fun i _ => hrow i)

omit [IsTopologicalRing K] [BorelSpace K] in
private theorem entrywise_integrable (g : Fin r → Fin s → K → ℂ)
    (Y : Matrix (Fin r) (Fin s) K)
    (hg : ∀ i j, Integrable (fun x => ψ.complex (x * Y i j) * g i j x) μ.measure) :
    Integrable
      (fun X : Matrix (Fin r) (Fin s) K =>
        (∏ i, ∏ j, g i j (X i j)) * ψ.complex (rectangularPairing X Y))
      (RankinSelberg.rectangularMeasure μ r s) := by
  simp_rw [entrywise_kernel]
  exact Integrable.fintype_prod (fun i => Integrable.fintype_prod (hg i))

end Tensor

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

variable {r s : ℕ}

/-- The actual entrywise affine lattice box, with independent integer levels. -/
def rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F.Carrier) :
    Set (Matrix (Fin r) (Fin s) F.Carrier) :=
  Set.univ.pi fun i => Set.univ.pi fun j =>
    {x | x - A i j ∈ T.additiveLattice (m i j)}

@[simp] theorem mem_rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A X : Matrix (Fin r) (Fin s) F.Carrier) :
    X ∈ rectangularLatticeCoset F T m A ↔
      ∀ i j, X i j - A i j ∈ T.additiveLattice (m i j) := by
  change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ,
    X i j - A i j ∈ T.additiveLattice (m i j)) ↔ _
  simp only [Set.mem_univ, forall_const]

private theorem coset_compact (m : ℤ) (a : F.Carrier) :
    letI := T.topology
    IsCompact {x : F.Carrier | x - a ∈ T.additiveLattice m} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hC : {x : F.Carrier | x - a ∈ T.additiveLattice m} =
      (fun t => t + a) '' (T.additiveLattice m : Set F.Carrier) := by
    ext x
    constructor
    · intro hx
      exact ⟨x - a, hx, sub_add_cancel x a⟩
    · rintro ⟨t, ht, rfl⟩
      simpa only [Set.mem_ofPred_eq, add_sub_cancel_right, SetLike.mem_coe] using ht
  rw [hC]
  exact (T.isCompact_additiveLattice m).image (continuous_id.add continuous_const)

/-- Entrywise affine lattice boxes are compact, including empty dimensions. -/
theorem isCompact_rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F.Carrier) :
    letI := T.topology
    IsCompact (rectangularLatticeCoset F T m A) := by
  let := T.topology
  exact isCompact_univ_pi fun i =>
    isCompact_univ_pi fun j => coset_compact F T (m i j) (A i j)

/-- Entrywise affine lattice boxes are clopen. -/
theorem isClopen_rectangularLatticeCoset (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F.Carrier) :
    letI := T.topology
    IsClopen (rectangularLatticeCoset F T m A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  refine ⟨(isCompact_rectangularLatticeCoset F T m A).isClosed, ?_⟩
  exact isOpen_set_pi Set.finite_univ fun i _ =>
    isOpen_set_pi Set.finite_univ fun j _ =>
      (T.isOpen_additiveLattice (m i j)).preimage (continuous_id.sub continuous_const)

/-- The characteristic function of the actual affine lattice box, as a
Schwartz–Bruhat test on the full rectangular matrix space. -/
def rectangularLatticeCosetTest (m : Fin r → Fin s → ℤ)
    (A : Matrix (Fin r) (Fin s) F.Carrier) :
    letI := T.topology
    SchwartzBruhat (Matrix (Fin r) (Fin s) F.Carrier) := by
  letI := T.topology
  exact Hecke.TestFunction.characteristic
    (isClopen_rectangularLatticeCoset F T m A)
    (isCompact_rectangularLatticeCoset F T m A)

@[simp] theorem rectangularLatticeCosetTest_apply (m : Fin r → Fin s → ℤ)
    (A X : Matrix (Fin r) (Fin s) F.Carrier) :
    letI := T.topology
    rectangularLatticeCosetTest F T m A X =
      (rectangularLatticeCoset F T m A).indicator (fun _ => (1 : ℂ)) X := rfl

set_option backward.isDefEq.respectTransparency false in
theorem rectangularLatticeCoset_indicator (m : Fin r → Fin s → ℤ)
    (A X : Matrix (Fin r) (Fin s) F.Carrier) :
    (rectangularLatticeCoset F T m A).indicator (fun _ => (1 : ℂ)) X =
      ∏ i, ∏ j,
        {x : F.Carrier | x - A i j ∈ T.additiveLattice (m i j)}.indicator
          (fun _ => (1 : ℂ)) (X i j) := by
  calc
    _ = ∏ i, (Set.univ.pi fun j =>
          {x : F.Carrier | x - A i j ∈ T.additiveLattice (m i j)}).indicator
        (fun _ => (1 : ℂ)) (X i) :=
      indicator_pi_one
        (fun i => Set.univ.pi fun j =>
          {x : F.Carrier | x - A i j ∈ T.additiveLattice (m i j)}) X
    _ = _ := Finset.prod_congr rfl fun i _ => indicator_pi_one _ _

/-- The exact product of scalar lattice masses for the supplied Haar measure. -/
def rectangularLatticeVolume :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    AdditiveHaarMeasure F.Carrier → (Fin r → Fin s → ℤ) → ℂ := by
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  intro μ m
  exact ∏ i, ∏ j, ((μ.measure (T.additiveLattice (m i j) : Set F.Carrier)).toReal : ℂ)

/-- The actual Fourier integrand of an affine lattice box is integrable for
every supplied additive Haar measure. -/
theorem rectangularLatticeCoset_fourierIntegrable :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (m : Fin r → Fin s → ℤ) (A Y : Matrix (Fin r) (Fin s) F.Carrier),
    Integrable
      (fun X => rectangularLatticeCosetTest F T m A X *
        ψ.complex (rectangularPairing X Y))
      (RankinSelberg.rectangularMeasure μ r s) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ m A Y
  simp_rw [rectangularLatticeCosetTest_apply, rectangularLatticeCoset_indicator]
  exact entrywise_integrable ψ μ _ Y fun i j =>
    (padicLatticeFourier F T ψ μ (m i j) (A i j) (Y i j)).1

/-- The plus rectangular Fourier integral of an actual affine lattice box.
The dual entry level is the conductor minus the original level; the phase and
all volumes use the same supplied character and scalar Haar measure. -/
theorem rectangularLatticeCoset_fourierIntegral :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (m : Fin r → Fin s → ℤ) (A Y : Matrix (Fin r) (Fin s) F.Carrier),
    rectangularFourierIntegral ψ μ (rectangularLatticeCosetTest F T m A) Y =
      rectangularLatticeVolume F T μ m * ψ.complex (rectangularPairing A Y) *
        (rectangularLatticeCoset F T (fun i j => T.additiveConductor ψ - m i j) 0).indicator
          (fun _ => (1 : ℂ)) Y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ m A Y
  have htest : (rectangularLatticeCosetTest F T m A :
      Matrix (Fin r) (Fin s) F.Carrier → ℂ) =
      fun X => ∏ i, ∏ j,
        {x : F.Carrier | x - A i j ∈ T.additiveLattice (m i j)}.indicator
          (fun _ => (1 : ℂ)) (X i j) := by
    funext X
    rw [rectangularLatticeCosetTest_apply]
    exact rectangularLatticeCoset_indicator F T m A X
  rw [htest, entrywise_fourierIntegral]
  calc
    (∏ i, ∏ j, fourierIntegral ψ μ
        ({x : F.Carrier | x - A i j ∈ T.additiveLattice (m i j)}.indicator
          (fun _ => (1 : ℂ))) (Y i j)) =
        ∏ i, ∏ j,
          ((μ.measure (T.additiveLattice (m i j) : Set F.Carrier)).toReal : ℂ) *
            ψ.complex (A i j * Y i j) *
            (T.additiveLattice (T.additiveConductor ψ - m i j) : Set F.Carrier).indicator
              (fun _ => (1 : ℂ)) (Y i j) := by
      apply Finset.prod_congr rfl
      intro i _
      exact Finset.prod_congr rfl fun j _ =>
        (padicLatticeFourier F T ψ μ (m i j) (A i j) (Y i j)).2
    _ = _ := by
      rw [rectangularLatticeCoset_indicator]
      simp only [rectangularLatticeVolume, rectangularPairing,
        character_sum, Matrix.zero_apply, sub_zero]
      simp only [Finset.prod_mul_distrib]
      rfl

end Padic

end Langlands.HarmonicAnalysis
