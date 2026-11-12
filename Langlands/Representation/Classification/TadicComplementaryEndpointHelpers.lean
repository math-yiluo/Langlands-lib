import Langlands.Representation.Classification.TadicComplementarySeriesStatement
import Langlands.Representation.Classification.TadicComplementaryEndpointRegularityStatement
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Classification.ExponentFamily
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Induction.CompactQuotientTwistTrace
import Langlands.Group.GL.CompactOpen
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Actual complementary-product endpoint adapters

Admissibility, finite length, and continuity of distribution characters for
Tadic's actual normalized two-block complementary product.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData HarmonicAnalysis MeasureTheory
open scoped NNReal _root_.Topology

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every real complementary product of an admissible block is admissible. -/
theorem complementaryProduct_admissible {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.representation) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (2 * n)
    IsAdmissible (complementaryProduct F T hn A s).representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (2 * n)
  let B := BlockShape.uniform 2 n hn
  have hf : ∀ i, IsAdmissible (T.twistedBlocks B (fun _ => A)
      (fun i => if (i : ℕ) = 0 then s else -s) i).representation := by
    intro i
    exact (isAdmissible_twist_iff _ _
      (T.isOpen_ker_determinantPowerCharacter _ _)).mpr hA
  exact Parabolic.normalizedInductionAdmissibility F T _ _ _
    (FiniteTensor.isAdmissible_external _ hf)

/-- Every real complementary product of an irreducible block has finite
composition length, including reducible endpoint parameters. -/
theorem complementaryProduct_finiteLength {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) (s : ℝ) :
    letI := T.topology
    (complementaryProduct F T hn A s).HasFiniteLength := by
  letI := T.topology
  exact irreducibleProductFiniteLength.{uF, max uF uV} F T (2 * n) (by omega)
    (BlockShape.uniform 2 n hn) _
    (fun i => (SmoothRep.isIrreducible_twist_iff _
      (T.isOpen_ker_determinantPowerCharacter _ _) A).mpr hA)

/-- The exponent character is trivial on every compact subgroup of the
actual block parabolic. -/
private theorem exponentModulus_compact_trivial {n : ℕ} (B : BlockShape n)
    (u : Fin B.length → ℝ) :
    letI := T.topology
    ∀ (H : Subgroup (B.parabolic F.Carrier)),
      IsCompact (H : Set (B.parabolic F.Carrier)) → H ≤ (T.exponentModulus B u).ker := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro H hH q hq
  have hdet (i : Fin B.length) :
      T.determinantNorm (B.size i) (B.leviProjection F.Carrier q i) = 1 := by
    let χ : B.parabolic F.Carrier →* ℝ≥0ˣ := (T.determinantNorm (B.size i)).comp
      ((Pi.evalMonoidHom (fun j => GeneralLinear (B.size j) F.Carrier) i).comp
        (B.leviProjection F.Carrier))
    have hχ : Continuous χ :=
      (T.determinantNormContinuous (B.size i)).continuous.comp
        ((continuous_apply i).comp (B.leviProjectionContinuous F.Carrier).continuous)
    exact RankinSelberg.LastRowReduction.eq_one_of_isCompact χ hχ H hH hq
  change T.exponentModulus B u q = 1
  apply Units.ext
  rw [T.coe_exponentModulus, Units.val_one]
  apply Finset.prod_eq_one
  intro i _
  rw [hdet i, Units.val_one, NNReal.one_rpow]

/-- The actual induced model with real-power exponent character is equivalent
to Tadic's actual complementary-product representation. -/
private theorem complementaryProduct_realPowerEquiv {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (2 * n)
    let B := BlockShape.uniform 2 n hn
    let σ := twist (T.parabolicHalfModulus B)
      ((B.blockTensor (fun _ => A.representation)).comp (B.leviProjection F.Carrier))
    Nonempty ((Induction.smoothInduced (B.parabolic F.Carrier)
      (realPowerTwist (T.exponentModulus B
        (fun i => if (i : ℕ) = 0 then 1 else -1)) s σ)).Equiv
      (complementaryProduct F T hn A s).representation) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (2 * n)
  have h := T.realPowerTwist_exponentModulus (BlockShape.uniform 2 n hn)
    (fun _ => A.representation) (fun i => if (i : ℕ) = 0 then 1 else -1) s
  simp_rw [mul_ite, mul_one, mul_neg_one] at h
  exact ⟨Induction.smoothInducedEquiv _ (equivOfRepresentationEq h)⟩

/-- Each actual distribution-character value of the complementary family is
continuous in its real parameter. The measure is any locally finite left
invariant measure; no endpoint irreducibility is required. -/
theorem continuous_complementaryProduct_distribution {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.representation) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (2 * n)
    letI := T.generalLinearT2Space (2 * n)
    letI := T.generalLinearLocallyCompactSpace (2 * n)
    letI := T.generalLinearNonarchimedean (2 * n)
    letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
    ∀ (μ : Measure (GeneralLinear (2 * n) F.Carrier))
      [IsFiniteMeasureOnCompacts μ] [Measure.IsMulLeftInvariant μ]
      (f : SchwartzBruhat (GeneralLinear (2 * n) F.Carrier)),
      Continuous (fun s : ℝ => Character.distribution μ
        (complementaryProduct F T hn A s).representation
        (complementaryProduct_admissible F T hn A hA s) f) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (2 * n)
  letI := T.generalLinearT2Space (2 * n)
  letI := T.generalLinearLocallyCompactSpace (2 * n)
  letI := T.generalLinearNonarchimedean (2 * n)
  letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
  letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
  intro μ _ _ f
  let B := BlockShape.uniform 2 n hn
  let u : Fin B.length → ℝ := fun i => if (i : ℕ) = 0 then 1 else -1
  let σ := twist (T.parabolicHalfModulus B)
    ((B.blockTensor (fun _ => A.representation)).comp (B.leviProjection F.Carrier))
  let χ : ℝ → B.parabolic F.Carrier →* ℂˣ :=
    fun s => realPowerCharacter (T.exponentModulus B u) s
  have hσ : IsAdmissible σ :=
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
      ((Parabolic.leviInflationAdmissibility F T B _ _).mpr
        (FiniteTensor.isAdmissible_external (fun _ => A.representation) (fun _ => hA)))
  letI : CompactSpace (Induction.LeftQuotient (B.parabolic F.Carrier)) :=
    Parabolic.parabolicQuotientCompact F T B
  let E (s : ℝ) := Classical.choice (complementaryProduct_realPowerEquiv F T hn A s)
  have hAdm (s : ℝ) : IsAdmissible
      (Induction.smoothInduced (B.parabolic F.Carrier) (twist (χ s) σ)) :=
    isAdmissible_of_equiv (E s).symm (complementaryProduct_admissible F T hn A hA s)
  have hχ (s : ℝ) (H : Subgroup (B.parabolic F.Carrier))
      (hH : IsCompact (H : Set (B.parabolic F.Carrier))) : H ≤ (χ s).ker :=
    le_trans (exponentModulus_compact_trivial F T B u H hH)
      (ker_le_realPowerCharacter_ker _ s)
  have hEval (q : B.parabolic F.Carrier) : Continuous (fun s : ℝ => (χ s q : ℂ)) := by
    let r := T.exponentModulus B u q
    have hr : (0 : ℝ) < ((r : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr r.ne_zero : (0 : ℝ≥0) < (r : ℝ≥0))
    change Continuous (fun s : ℝ => Complex.ofReal (((r : ℝ≥0) : ℝ) ^ s))
    exact Complex.continuous_ofReal.comp (Real.continuous_const_rpow hr.ne')
  have hc := Induction.continuous_induced_distribution_twist μ
    (B.parabolic F.Carrier) (by
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      exact B.isClosed_parabolic F.Carrier)
    σ hσ χ hχ hEval hAdm f
  have he (s : ℝ) : Character.distribution μ
      (Induction.smoothInduced (B.parabolic F.Carrier) (twist (χ s) σ)) (hAdm s) f =
        Character.distribution μ (complementaryProduct F T hn A s).representation
          (complementaryProduct_admissible F T hn A hA s) f := by
    exact congrArg (fun D : Distribution (GeneralLinear (2 * n) F.Carrier) => D f)
      (Character.distribution_eq_of_equivariant μ _ (hAdm s) _
        (complementaryProduct_admissible F T hn A hA s) (E s).toLinearEquiv
        (Representation.IntertwiningMap.isIntertwining _ _ (E s).toIntertwiningMap))
  exact hc.congr he

/-- The grouped endpoint-regularity target, with independent universes. -/
theorem complementaryEndpointRegularity :
    ComplementaryEndpointRegularity.{uF, uV} F T := by
  letI := T.topology
  intro n hn A
  letI := T.generalLinearTopologicalGroup (2 * n)
  letI := T.generalLinearT2Space (2 * n)
  letI := T.generalLinearLocallyCompactSpace (2 * n)
  letI := T.generalLinearNonarchimedean (2 * n)
  letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
  letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
  intro hA
  refine ⟨complementaryProduct_admissible F T hn A hA, ?_, ?_⟩
  · intro hirr s
    exact complementaryProduct_finiteLength F T hn A hirr s
  · intro hπ μ _ _ f
    exact continuous_complementaryProduct_distribution F T hn A hA μ f

end Langlands.Classification
