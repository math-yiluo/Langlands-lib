import Langlands.BaseChange.CommonShintaniLiftTrace
import Langlands.BaseChange.CyclicAlgebraDeterminant
import Langlands.BaseChange.EllipticTransfer
import Langlands.BaseChange.RegularSigmaLiftSquareIntegrableStatement
import Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentity.NormDeterminantCutoff
import Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison
import Langlands.JacquetLanglands.UnitarizableEssentiallySquareIntegrable
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.Representation.Classification.GenericEllipticCharacter

/-!
# Square-integrability of a regular σ-descent from σ-elliptic nonvanishing

This module proves that `SigmaDiscreteEllipticNonvanishingStatement` implies
`RegularSigmaLiftSquareIntegrableStatement`. A σ-elliptically supported test function with
nonzero twisted trace is transferred to an elliptically supported concordant function
(`ellipticTransfer`), cut to the matrices whose determinant is a norm; the regular σ-lift
identity then gives an elliptically supported function with nonzero trace for `π`. A generic
representation that is not essentially square-integrable has vanishing character on the
regular elliptic set (`padicGenericEllipticCharacterVanishing`), so `π` is essentially
square-integrable, and unitarizability removes the real twist. This follows Henniart–Lemaire
(2011), II.4.8, and Arthur–Clozel (1989), Chapter 1, Lemmas 2.11–2.12. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Langlands.JacquetLanglands ConcordanceLocalization

/-- The σ-elliptic nonvanishing of twisted traces of σ-discrete series
(`SigmaDiscreteEllipticNonvanishingStatement`, at the universes of the base field, the
extension field and the carrier of the σ-discrete series) implies
`RegularSigmaLiftSquareIntegrableStatement` at the same universes and every carrier universe
`uV` of the descended representation. -/
def RegularSigmaLiftSquareIntegrableFromEllipticNonvanishingStatement.{u, v, uV, uW} : Prop :=
  SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW} →
    RegularSigmaLiftSquareIntegrableStatement.{u, v, uV, uW}

universe u v uV uW

/-- `SigmaDiscreteEllipticNonvanishingStatement` implies
`RegularSigmaLiftSquareIntegrableStatement` (Henniart–Lemaire 2011, II.4.8; Arthur–Clozel
1989, Chapter 1, Lemmas 2.11–2.12). -/
theorem regularSigmaLiftSquareIntegrableFromEllipticNonvanishing :
    RegularSigmaLiftSquareIntegrableFromEllipticNonvanishingStatement.{u, v, uV, uW} := by
  intro hnonvanishing F _ _ _ _ _ E _ _ _ _ _ σ l r hσ
  have : Module.Finite F E := hσ.1
  have := LocalFieldTopology.generalLinear_t2Space F (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (r + 1)
  have := generalLinear_t2Space_of_finite F E (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
  intro W _ _ ρ hρ hdisc A V _ _ π hπ ψ hgen hunit c hlift
  let _ : MeasurableSpace (GeneralLinear (r + 1) F) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
  let _ : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
  have _ : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
  let μF : Measure (GeneralLinear (r + 1) F) := Measure.haar
  have : μF.IsHaarMeasure := by dsimp [μF]; infer_instance
  let μE : Measure (GeneralLinear (r + 1) E) := Measure.haar
  have : μE.IsHaarMeasure := by dsimp [μE]; infer_instance
  -- A σ-elliptically supported test function with nonzero twisted trace.
  obtain ⟨φ, hφell, hφ⟩ := hnonvanishing F E σ l r hσ ρ hρ hdisc A μE
  -- An elliptically supported concordant function, cut to norm determinants.
  obtain ⟨f, hfell, hconc⟩ :=
    (ellipticTransfer F E σ l (r + 1) hσ μF μE inferInstance inferInstance).1 φ hφell
  let N : Set Fˣ := ((Units.map (Algebra.norm F : E →* F)).range : Set Fˣ)
  have hN : IsClopen N := isClopen_normUnitsRange (hσ.2.1 ▸ hσ.pos.ne')
  have hdet : Continuous (GeneralLinear.determinant : GeneralLinear (r + 1) F → Fˣ) :=
    Matrix.GeneralLinearGroup.continuous_det
  let fN := cutoff (hN.preimage hdet) f
  have hconcN : AreConcordant σ l μF μE φ fN :=
    concordant_cutoff_ordinary hconc hdet
      (fun x g => by rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul])
      hN (fun δ' γ' h => ⟨GeneralLinear.determinant δ', h.norm_determinant_units_eq hσ⟩)
  have hsuppN : Function.support fN = Function.support f ∩ GeneralLinear.determinant ⁻¹' N :=
    support_cutoff _ f
  have hfNell : IsEllipticSupported (fN : GeneralLinear (r + 1) F → ℂ) := by
    intro g hg
    have hg' : g ∈ Function.support fN := hg
    rw [hsuppN] at hg'
    exact hfell g hg'.1
  have hdetN : ∀ g : GeneralLinear (r + 1) F, fN g ≠ 0 →
      GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : E →* F)).range := by
    intro g hg
    have hg' : g ∈ Function.support fN := hg
    rw [hsuppN] at hg'
    exact hg'.2
  -- The regular σ-lift identity gives a nonzero trace of `π` on `fN`.
  have htrace := hlift.2 μF μE φ fN hconcN hφell.isSigmaRegularSupported
    hfNell.isRegularSupported hdetN
  have hne : Character.distribution μF π hπ fN ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at htrace
    exact hφ htrace
  -- A generic representation with nonzero elliptic trace is essentially square-integrable.
  have hess : IsEssentiallySquareIntegrable π := by
    by_contra hnot
    have hnotp : ¬ (CharZeroLocalField.topologicalData F).IsEssentiallySquareIntegrable π :=
      fun h => hnot ((isEssentiallySquareIntegrable_iff_padic
        (CharZeroLocalField.topologicalData F) π).mpr h)
    have hvan : ∀ g : GeneralLinear (r + 1) F, IsRegularElliptic g →
        HasCharacterValue π hπ g 0 := fun g hg =>
      padicGenericEllipticCharacterVanishing (CharZeroLocalField.residueChar F)
        (CharZeroLocalField.padicField F) (CharZeroLocalField.topologicalData F) r ψ V π
        hgen hnotp g hg
    exact hne (distribution_eq_zero_of_localValues_zero fun x hx => hvan x (hfNell x hx) μF)
  -- Unitarizability removes the real twist.
  exact hess.isSquareIntegrable_of_isUnitarizable (Nat.succ_pos r) hgen.1 hunit

end Langlands.BaseChange
