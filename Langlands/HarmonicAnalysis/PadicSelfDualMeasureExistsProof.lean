import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement
import Langlands.HarmonicAnalysis.PadicLatticeHaarProof
import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionProof

/-! Scalar self-dual Haar existence by finite lattice-coset Fourier inversion. -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe u

section FiniteLinearity

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]

omit [IsTopologicalRing K] [BorelSpace K] in
private theorem fourierIntegral_finite_linear_combination
    {ι : Type*} [Fintype ι] (ψ : UnitaryAdditiveCharacter K)
    (μ : AdditiveHaarMeasure K) (c : ι → ℂ) (g : ι → K → ℂ) (y : K)
    (hg : ∀ i, Integrable (fun x => ψ.complex (x * y) * g i x) μ.measure) :
    fourierIntegral ψ μ (fun x => ∑ i, c i * g i x) y =
      ∑ i, c i * fourierIntegral ψ μ (g i) y := by
  classical
  unfold fourierIntegral
  simp_rw [Finset.mul_sum, mul_left_comm (ψ.complex _) (c _)]
  rw [integral_finsetSum Finset.univ (fun i _ => (hg i).const_mul (c i))]
  simp_rw [integral_const_mul]

end FiniteLinearity

/-- Every supplied p-adic topology admits a self-dual regular additive Haar
measure for each continuous nontrivial unitary additive character. -/
theorem padicSelfDualMeasureExists {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicSelfDualMeasureExistsStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  refine ⟨(padicLatticeGeometry F T).1, ?_⟩
  let := (padicLatticeGeometry F T).1
  intro ψ
  obtain ⟨μ, hμ⟩ := (padicLatticeHaar F T).2 ψ
  refine ⟨μ, ?_⟩
  classical
  let I (m : ℤ) (a : F.Carrier) : F.Carrier → ℂ :=
    {z : F.Carrier | z - a ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))
  let M (m : ℤ) : ℂ :=
    ((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ)
  have hzero (k : ℤ) :
      I k 0 = (T.additiveLattice k : Set F.Carrier).indicator (fun _ => (1 : ℂ)) := by
    have he : {z : F.Carrier | z - 0 ∈ T.additiveLattice k} =
        (T.additiveLattice k : Set F.Carrier) := by
      ext z
      simp
    exact congrArg (fun s : Set F.Carrier => s.indicator (fun _ => (1 : ℂ))) he
  have hI (m : ℤ) (a y : F.Carrier) :
      Integrable (fun x => ψ.complex (x * y) * I m a x) μ.measure ∧
      fourierIntegral ψ μ (I m a) y =
        M m * ψ.complex (a * y) * I (T.additiveConductor ψ - m) 0 y := by
    rw [hzero]
    simpa only [I, M] using
      (padicLatticeFourier F T) ψ μ m a y
  have hmass (m : ℤ) : M m * M (T.additiveConductor ψ - m) = 1 := by
    dsimp [M]
    exact_mod_cast (hμ m).2
  have htwice (m : ℤ) (a x : F.Carrier) :
      Integrable (fun y => ψ.complex (y * x) *
        fourierIntegral ψ μ (I m a) y) μ.measure ∧
      fourierIntegral ψ μ (fourierIntegral ψ μ (I m a)) x = I m a (-x) := by
    have hphase (y : F.Carrier) :
        ψ.complex (y * x) * fourierIntegral ψ μ (I m a) y =
          M m * (ψ.complex (y * (x + a)) *
            I (T.additiveConductor ψ - m) 0 y) := by
      rw [(hI m a y).2, mul_add, ψ.complex.map_add_eq_mul, mul_comm y a]
      ring
    refine ⟨((hI (T.additiveConductor ψ - m) 0 (x + a)).1.const_mul (M m)).congr
      (ae_of_all _ fun y => (hphase y).symm), ?_⟩
    calc
      fourierIntegral ψ μ (fourierIntegral ψ μ (I m a)) x =
          ∫ y, M m * (ψ.complex (y * (x + a)) *
            I (T.additiveConductor ψ - m) 0 y) ∂μ.measure :=
        integral_congr_ae (ae_of_all _ hphase)
      _ = M m * fourierIntegral ψ μ
          (I (T.additiveConductor ψ - m) 0) (x + a) :=
        integral_const_mul _ _
      _ = I m a (-x) := by
        rw [(hI (T.additiveConductor ψ - m) 0 (x + a)).2]
        have hn : T.additiveConductor ψ - (T.additiveConductor ψ - m) = m := by omega
        rw [hn]
        simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
        rw [← mul_assoc, hmass, one_mul]
        simp only [I, Set.indicator, Set.mem_ofPred_eq, sub_zero,
          show -x - a = -(x + a) by abel, neg_mem_iff]
  intro f
  obtain ⟨m, N, c, a, hf⟩ := (padicLatticeSchwartzExpansion F T) f
  have hfext : (f : F.Carrier → ℂ) = fun x => ∑ i : Fin N, c i * I m (a i) x :=
    funext hf
  have hF (y : F.Carrier) :
      fourierTransform ψ μ f y = ∑ i : Fin N,
        c i * fourierIntegral ψ μ (I m (a i)) y := by
    change fourierIntegral ψ μ (f : F.Carrier → ℂ) y = _
    rw [hfext]
    exact fourierIntegral_finite_linear_combination ψ μ c (fun i => I m (a i)) y
      (fun i => (hI m (a i) y).1)
  refine ⟨?_, ?_⟩
  · intro y
    have hs := integrable_finsetSum Finset.univ
      (fun (i : Fin N) _ => (htwice m (a i) y).1.const_mul (c i))
    apply hs.congr
    refine ae_of_all _ fun x => ?_
    change (∑ i : Fin N, c i *
      (ψ.complex (x * y) * fourierIntegral ψ μ (I m (a i)) x)) =
      ψ.complex (x * y) * fourierTransform ψ μ f x
    rw [hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro x
    rw [show fourierTransform ψ μ f = fun y => ∑ i : Fin N,
        c i * fourierIntegral ψ μ (I m (a i)) y from funext hF]
    rw [fourierIntegral_finite_linear_combination ψ μ c
      (fun i => fourierIntegral ψ μ (I m (a i))) x
      (fun i => (htwice m (a i) x).1)]
    calc
      (∑ i : Fin N, c i *
          fourierIntegral ψ μ (fourierIntegral ψ μ (I m (a i))) x) =
          ∑ i : Fin N, c i * I m (a i) (-x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(htwice m (a i) x).2]
      _ = f (-x) := (hf (-x)).symm

end Langlands.HarmonicAnalysis
