import Langlands.BaseChange.CyclicAlgebraDeterminant
import Langlands.BaseChange.SigmaDiscreteRegularDescentStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Forward
import Langlands.BaseChange.SigmaLiftCharacterIdentity.NormDeterminantCutoff

/-!
# From the regular σ-lift identity to the Shintani identity

The trace identity on σ-regularly and regularly supported concordant pairs, with the
determinants on the ordinary support in the image of the norm, gives the identity of local
character values at every norm-associated pair with a regular semisimple ordinary element.
The argument follows the forward direction of Henniart–Lemaire (2011), II.2.9, and adds a
cutoff of the ordinary test function by the norm image of the determinant.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis
open ConcordanceLocalization

namespace SigmaLiftCharacterIdentity

/-- Under the five premises of `SigmaLiftCharacterIdentityForwardStatement`, the regular
σ-lift identity `IsRegularSigmaLift` implies the Shintani identity `IsShintaniLift` for the
same intertwiner and constant (Henniart–Lemaire II.2.9 and II.6.13). -/
theorem isShintaniLift_of_isRegularSigmaLift.{u, v, uV, uW}
    (hregularF : TwistedCharacterRegularValuesStatement.{u, u, uV})
    (hregularE : TwistedCharacterRegularValuesStatement.{u, v, uW})
    (htransfer : RegularTransferStatement.{u, v})
    (hintegrals : ConcordantIntegralEqualityStatement.{u, v})
    (hopen : SigmaRegularOpenStatement.{u, v})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ)
    (hE : IsCyclicAlgebra σ l) :
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      π.IsIrreducible → τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (c : ℂ),
        IsRegularSigmaLift σ l π hπ τ hτ A c → IsShintaniLift σ l π hπ τ hτ A c := by
  classical
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ τ hτ hπirr hτirr A c hreg
  refine ⟨hreg.1, ?_⟩
  intro δ γ hassoc hγ
  have hδ : IsSigmaRegular σ l δ := ⟨γ, hassoc, hγ⟩
  obtain ⟨a, ha⟩ := ordinary_regular_values F n hregularF π hπ hπirr γ hγ
  obtain ⟨b, hb⟩ := hregularE F E σ l n hE τ hτ hτirr A δ hδ
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let μF : Measure (GeneralLinear n F) := Measure.haar
  let μE : Measure (GeneralLinear n E) := Measure.haar
  have : μF.IsHaarMeasure := by dsimp [μF]; infer_instance
  have : μE.IsHaarMeasure := by dsimp [μE]; infer_instance
  obtain ⟨U, hU, hγU, hvalF⟩ := ha μF
  obtain ⟨Wδ, hWδ, hδW, hvalE⟩ := hb μE
  obtain ⟨K, hcK, hK, hδK, hKsub⟩ :=
    exists_isCompact_isClopen_subset (hWδ.inter (hopen F E σ l n hE)) ⟨hδW, hδ⟩
  let φ := Hecke.TestFunction.characteristic hK hcK
  have hφ : IsSigmaRegularSupported σ l φ := by
    change Function.support (φ : GeneralLinear n E → ℂ) ⊆ {d | IsSigmaRegular σ l d}
    rw [Hecke.TestFunction.support_characteristic]
    exact hKsub.trans Set.inter_subset_right
  obtain ⟨f, hfreg, hmatch⟩ := (htransfer F E σ l n hE μF μE).1 φ hφ
  -- Localize both functions by the characteristic polynomial coefficients.
  let qE (d : GeneralLinear n E) := coefficients (cyclicNorm σ l d)
  let qF (g : GeneralLinear n F) := coefficients (baseChange F E n g)
  have hqE : Continuous qE := continuous_coefficients.comp (continuous_cyclicNorm σ l)
  have hqF : Continuous qF := continuous_coefficients.comp continuous_baseChange
  have := finiteAlgebra_t2Space F E
  have := finiteAlgebra_locallyCompactSpace F E
  have := finiteAlgebra_totallyDisconnectedSpace F E
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  obtain ⟨B, hB, hγB, hfU⟩ := exists_cutoff_support hqF f (isOpen_conjugacySaturation hU)
    (y := qF γ) (by
      intro g _ hg
      have hpoly := charpoly_eq_of_baseChange_coefficients hE hg
      obtain ⟨x, hx⟩ := matrixConj_of_squarefree_charpoly_eq
        (γ : Matrix (Fin n) (Fin n) F) (g : Matrix (Fin n) (Fin n) F) hsep.squarefree hpoly.symm
      have hconj : x * γ * x⁻¹ = g := Units.ext hx
      rw [← hconj]
      exact conj_mem_conjugacySaturation hγU x)
  let φB := cutoff (hB.preimage hqE) φ
  let fB := cutoff (hB.preimage hqF) f
  have hmatchB : AreConcordant σ l μF μE φB fB :=
    concordant_cutoff hmatch hqE hqF (coefficients_cyclicNorm_conj hE.pow_eq_one)
      coefficients_baseChange_conj (fun _ _ h => coefficients_associated h) hB
  -- Cut the ordinary function by the norm image of the determinant.
  let N : Set Fˣ := ((Units.map (Algebra.norm F : E →* F)).range : Set Fˣ)
  have hN : IsClopen N := isClopen_normUnitsRange (hE.2.1 ▸ hE.pos.ne')
  have hdet : Continuous (GeneralLinear.determinant : GeneralLinear n F → Fˣ) :=
    Matrix.GeneralLinearGroup.continuous_det
  let fN := cutoff (hN.preimage hdet) fB
  have hmatchN : AreConcordant σ l μF μE φB fN :=
    concordant_cutoff_ordinary hmatchB hdet
      (fun x g => by rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul])
      hN (fun δ' γ' h => ⟨GeneralLinear.determinant δ', h.norm_determinant_units_eq hE⟩)
  have hsuppN : Function.support fN = (Function.support f ∩ qF ⁻¹' B) ∩
      GeneralLinear.determinant ⁻¹' N := by
    change Function.support (cutoff (hN.preimage hdet) (cutoff (hB.preimage hqF) f)) = _
    rw [support_cutoff, support_cutoff]
  have hφB : IsSigmaRegularSupported σ l φB := by
    intro d hd
    have hd' : d ∈ Function.support (cutoff (hB.preimage hqE) φ) := hd
    rw [support_cutoff, Hecke.TestFunction.support_characteristic] at hd'
    exact (hKsub hd'.1).2
  have hfN : IsRegularSupported fN := by
    intro g hg
    have hg' : g ∈ Function.support fN := hg
    rw [hsuppN] at hg'
    exact hfreg g hg'.1.1
  have hdetN : ∀ g : GeneralLinear n F, fN g ≠ 0 →
      GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : E →* F)).range := by
    intro g hg
    have hg' : g ∈ Function.support fN := hg
    rw [hsuppN] at hg'
    exact hg'.2
  have hfNU : Function.support fN ⊆ conjugacySaturation U := by
    change Function.support (cutoff (hN.preimage hdet) fB) ⊆ _
    rw [support_cutoff]
    exact Set.inter_subset_left.trans hfU
  have hφBW : Function.support φB ⊆ Wδ := by
    change Function.support (cutoff (hB.preimage hqE) φ) ⊆ Wδ
    rw [support_cutoff, Hecke.TestFunction.support_characteristic]
    exact Set.inter_subset_left.trans (hKsub.trans Set.inter_subset_left)
  have hnonzero : (∫ d, φB d ∂μE) ≠ 0 := by
    change (∫ d, cutoff (hB.preimage hqE) (Hecke.TestFunction.characteristic hK hcK) d ∂μE) ≠ 0
    rw [cutoff_characteristic]
    refine characteristic_integral_ne_zero μE _ _ ⟨δ, hδK, ?_⟩
    change coefficients (cyclicNorm σ l δ) ∈ B
    rw [coefficients_associated hassoc]
    exact hγB
  have h := hreg.2 μF μE φB fN hmatchN hφB hfN hdetN
  have hmass := hintegrals F E σ l n hE μF μE φB fN hmatchN
  rw [hvalE φB hφBW, evaluate_saturation hU hvalF fN hfNU, ← hmass, ← mul_assoc] at h
  have hab : b = c * a := mul_right_cancel₀ hnonzero h
  exact ⟨a, ha, hab ▸ hb⟩

end SigmaLiftCharacterIdentity

end Langlands.BaseChange
