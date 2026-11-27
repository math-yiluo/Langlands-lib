import Langlands.BaseChange.PseudoCoefficientExistenceReduction
import Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement
import Langlands.BaseChange.SigmaOrbitRealTwist
import Langlands.BaseChange.SquareIntegrableNotInduced
import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.BaseChange.TwistedSupercuspidalEllipticNonvanishingStatement
import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.LocalField.FiniteExtensionModuleTopology
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered

/-!
# σ-elliptic nonvanishing for σ-stable supercuspidals from the σ-discrete case

`TwistedSupercuspidalEllipticNonvanishingFromSigmaDiscreteStatement` states that
`SigmaDiscreteEllipticNonvanishingStatement` (the twisted trace of a σ-discrete series of
`GL_{r+1}(E)` is nonzero on some σ-elliptically supported test function) implies
`TwistedSupercuspidalEllipticNonvanishingStatement` (the same for an irreducible supercuspidal
representation of `GL_n(E)`, `0 < n`, with a σ-intertwiner), and
`twistedSupercuspidalEllipticNonvanishingFromSigmaDiscrete` proves it. An irreducible
supercuspidal `τ` has a real determinant twist `τ ⊗ |det|^t` that is unitarizable, hence
square-integrable, hence a σ-discrete series; its twisted trace is that of `τ` composed with
multiplication of test functions by `|det|^t` (Arthur–Clozel 1989, Chapter 1, §2.3 and
Lemma 2.12 (i)). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v uW

/-- The square-integrability of positive-rank unitarizable supercuspidals, stated for the
canonical topological data of a `p`-adic field, holds for any topological data on it. -/
private theorem unitarizableSupercuspidal_isSquareIntegrable_of_topologicalData {p : ℕ}
    [Fact p.Prime] {L : PadicField.{v} p} (S : L.TopologicalData) {n : ℕ} (hn : 0 < n) :
    letI := S.topology
    ∀ A : SupercuspidalRep.{v, uW} (F := L.Carrier) (n := n),
      IsUnitarizable A.obj.representation → S.IsSquareIntegrable A.obj.representation := by
  rw [S.eq_canonicalTopologicalData]
  exact Classification.unitarizableSupercuspidal_isSquareIntegrable L hn

section LocalField

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Over a nonarchimedean local field `E` of characteristic zero, an irreducible supercuspidal
representation `P` of `GL_n(E)`, `0 < n`, has an irreducible square-integrable twist
`P ⊗ |det|^t` for some real `t`, with the residue-normalized absolute value of `E`. -/
theorem exists_isSquareIntegrable_realPowerTwist [CharZero E] {n : ℕ} (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GeneralLinear n E) W)
    (hP : P.IsIrreducible) (hsc : IsSupercuspidal P) :
    ∃ t : ℝ,
      (realPowerTwist ((LocalFieldData.ofInstances E).determinantNorm n) t P).IsIrreducible ∧
      JacquetLanglands.IsSquareIntegrable
        (realPowerTwist ((LocalFieldData.ofInstances E).determinantNorm n) t P) := by
  obtain ⟨t, hQi, hQsc, hQu⟩ := exists_unitary_realPowerTwist P hn hP hsc
  let p := CharZeroLocalField.residueChar E
  let : Fact p.Prime := ⟨CharZeroLocalField.residueChar_prime E⟩
  let L := CharZeroLocalField.padicField E
  let S : L.TopologicalData := CharZeroLocalField.topologicalData E
  let Q := realPowerTwist ((LocalFieldData.ofInstances E).determinantNorm n) t P
  let A : SupercuspidalRep.{v, uW} (F := E) (n := n) := ⟨SmoothRep.of Q hQsc.1.1, hQi, hQsc⟩
  exact ⟨t, hQi, unitarizableSupercuspidal_isSquareIntegrable_of_topologicalData S hn A hQu⟩

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F E] [IsModuleTopology F E]

/-- The character `g ↦ |det g|^t` of `GL_n(E)` is invariant under the entrywise action of an
`F`-automorphism `σ` of `E`. -/
theorem realPowerCharacter_determinantNorm_entrywiseAut (σ : E ≃ₐ[F] E) (n : ℕ) (t : ℝ)
    (g : GeneralLinear n E) :
    realPowerCharacter ((LocalFieldData.ofInstances E).determinantNorm n) t
        (entrywiseAut σ n g) =
      realPowerCharacter ((LocalFieldData.ofInstances E).determinantNorm n) t g := by
  simp only [realPowerCharacter, MonoidHom.comp_apply, determinantNorm_entrywiseAut]

end LocalField

/-- The σ-elliptic nonvanishing of twisted traces of σ-discrete series implies that of σ-stable
irreducible supercuspidals (Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (i)). The three universe
parameters of the premise and of the conclusion agree. -/
def TwistedSupercuspidalEllipticNonvanishingFromSigmaDiscreteStatement : Prop :=
  SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW} →
    TwistedSupercuspidalEllipticNonvanishingStatement.{u, v, uW}

/-- Proof of `TwistedSupercuspidalEllipticNonvanishingFromSigmaDiscreteStatement`: give `E` its
local-field structure, twist `τ` by `χ = |det|^t` to an irreducible square-integrable `τ ⊗ χ`;
it is tempered, not induced from a proper block parabolic, and `A` is a σ-intertwiner of it, so
it is a σ-discrete series. A σ-elliptically supported `φ` with nonzero twisted trace for `τ ⊗ χ`
gives the σ-elliptically supported `χ φ` with the same nonzero twisted trace for `τ`. -/
theorem twistedSupercuspidalEllipticNonvanishingFromSigmaDiscrete :
    TwistedSupercuspidalEllipticNonvanishingFromSigmaDiscreteStatement.{u, v, uW} := by
  intro hSD F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
  let _ : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
  intro W _ _ τ hτ hirr A μ _
  -- `E`, a finite extension of `F` with its module topology, is a local field of
  -- characteristic zero.
  let _ : ValuativeRel E := LocalField.FiniteExtension.valuativeRel F E
  have _ : IsNonarchimedeanLocalField E :=
    LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  have _ : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨t, hQi, hQsq⟩ := exists_isSquareIntegrable_realPowerTwist (Nat.succ_pos r) τ hirr hτ
  let χ := realPowerCharacter ((LocalFieldData.ofInstances E).determinantNorm (r + 1)) t
  have hν : IsOpen (((LocalFieldData.ofInstances E).determinantNorm (r + 1)).ker :
      Set (GeneralLinear (r + 1) E)) :=
    (LocalFieldData.ofInstances E).isOpen_ker_determinantNorm (r + 1)
  have hχ : IsOpen (χ.ker : Set (GeneralLinear (r + 1) E)) :=
    isOpen_ker_realPowerCharacter _ hν t
  have hχσ : ∀ g, χ (entrywiseAut σ (r + 1) g) = χ g :=
    realPowerCharacter_determinantNorm_entrywiseAut σ (r + 1) t
  have hQadm : IsAdmissible (twist χ τ) := hQsq.isAdmissible
  let B : SigmaIntertwiner σ (r + 1) (twist χ τ) :=
    twistTwistedIntertwiner (entrywiseAut σ (r + 1)) χ hχσ A
  have hQSD : IsSigmaDiscreteSeries σ (r + 1) (twist χ τ) :=
    ⟨hQadm, hQi, isTemperedRep_of_isSquareIntegrable hQsq, ⟨B⟩,
      fun Bs hBs X _ _ Ξ hΞ _ =>
        squareIntegrableNotInduced E (r + 1) W (twist χ τ) hQi hQsq Bs hBs X Ξ hΞ⟩
  obtain ⟨φ, hφ, hne⟩ := hSD F E σ l r hE (twist χ τ) hQadm hQSD B μ
  refine ⟨characterMultiplyTest χ hχ φ, fun δ hδ => hφ δ (right_ne_zero_of_mul hδ), ?_⟩
  have h := LinearMap.congr_fun
    (twistedDistribution_twist_eq_comp μ τ hτ.1 A.toLinearMap χ hχ hQadm) φ
  rw [LinearMap.comp_apply] at h
  rw [← h]
  exact hne

end Langlands.BaseChange
