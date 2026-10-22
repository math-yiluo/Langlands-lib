import Langlands.LocalFactor.CommonClosureWeilDeligneTransport
import Langlands.ClassFieldTheory.Local.ExtensionValuationTransport
import Langlands.Weil.Local.AssemblyProof

/-! # Actual Frobenius and spectral transport to the standalone extension -/

noncomputable section

universe uF uE uV

namespace Langlands.LocalFactor.CommonClosureWeilDeligne.Transport

open Weil.Local LocalClassField

variable {p : ℕ} [Fact p.Prime]
  (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The actual image-field cardinality is the standalone extension cardinality. -/
theorem residueCardinality_eq :
    residueCardinality F (extensionFiniteIntermediate F E f) =
      (E.canonicalTopologicalData.residueCardinality : ℝ) := by
  change ((LocalClassField.CommonClosure.canonicalData F
    (extensionFiniteIntermediate F E f)).residueCardinality : ℝ) = _
  exact_mod_cast extensionIntermediate_residueCardinality F E f

/-- The corresponding complex cardinality units agree. -/
theorem residueCardinalityUnit_eq :
    residueCardinalityUnit (CommonClosure.fieldData F (extensionFiniteIntermediate F E f)) =
      residueCardinalityUnit E.canonicalTopologicalData := by
  apply Units.ext
  simp only [residueCardinalityUnit_val]
  exact_mod_cast extensionIntermediate_residueCardinality F E f

private theorem standalone_norm_eq_iff_degree_one (w : localWeilGroup E) :
    localNormCharacter E w = (residueCardinalityUnit E.canonicalTopologicalData)⁻¹ ↔
      localDegree E w = Multiplicative.ofAdd (1 : ℤ) := by
  constructor
  · intro hw
    have hv := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) hw
    simp only [localNormCharacter_apply, norm_zpow, Complex.norm_natCast,
      Units.val_inv_eq_inv_val, residueCardinalityUnit_val, norm_inv] at hv
    have hq : (1 : ℝ) < (E.canonicalTopologicalData.residueCardinality : ℝ) := by
      exact_mod_cast E.canonicalTopologicalData.residueCardinality_gt_one
    have hn := zpow_right_injective₀ (lt_trans zero_lt_one hq) (ne_of_gt hq)
      (hv.trans (zpow_neg_one _).symm)
    change localDegreeInt E w = 1
    exact neg_injective hn
  · intro hw
    apply Units.ext
    exact residueNormCharacter_degree_one E.canonicalTopologicalData (localDegree E) hw

/-- The actual Weil equivalence identifies degree-one lifts with the image-field
norm-defined geometric Frobenius subtype. -/
def geometricFrobeniusEquiv :
    {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)} ≃
      GeometricFrobenius F (extensionFiniteIntermediate F E f) where
  toFun w := ⟨extensionImageWeilEquiv F E f w.val, by
    exact (extensionImageWeilEquiv_normCharacter F E f w.val).trans
      (((standalone_norm_eq_iff_degree_one E w.val).mpr w.property).trans
        (congrArg Inv.inv (residueCardinalityUnit_eq F E f).symm))⟩
  invFun w := ⟨(extensionImageWeilEquiv F E f).symm w.val, by
    apply (standalone_norm_eq_iff_degree_one E _).mp
    have hn := extensionImageWeilEquiv_normCharacter F E f
      ((extensionImageWeilEquiv F E f).symm w.val)
    rw [(extensionImageWeilEquiv F E f).apply_symm_apply] at hn
    exact hn.symm.trans (w.property.trans
      (congrArg Inv.inv (residueCardinalityUnit_eq F E f)))⟩
  left_inv w := Subtype.ext ((extensionImageWeilEquiv F E f).symm_apply_apply w.val)
  right_inv w := Subtype.ext ((extensionImageWeilEquiv F E f).apply_symm_apply w.val)

@[simp]
theorem geometricFrobeniusEquiv_val
    (w : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)}) :
    (geometricFrobeniusEquiv F E f w).val = extensionImageWeilEquiv F E f w.val := rfl

/-- A positive real cardinality for the actual standalone field. -/
theorem standalone_residueCardinality_pos :
    (0 : ℝ) < (E.canonicalTopologicalData.residueCardinality : ℝ) := by
  exact_mod_cast lt_trans Nat.zero_lt_one E.canonicalTopologicalData.residueCardinality_gt_one

/-- Intrinsic spectral coordinates agree, with no supplied equality of cardinalities. -/
theorem spectralParameter_eq (s : ℂ) :
    spectralParameter (residueCardinality F (extensionFiniteIntermediate F E f))
      (residueCardinality_pos F (extensionFiniteIntermediate F E f)) s =
    spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
      (standalone_residueCardinality_pos E) s := by
  simp only [spectralParameter, residueCardinality_eq]

/-- Actual geometric Frobenius gives the same rational L-factor. -/
theorem rationalLFactor_geometricFrobenius
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)}) :
    WeilDeligne.rationalLFactor (standalonePair F E f A) (localInertia E) Φ.val =
      rationalLFactor F (extensionFiniteIntermediate F E f) A
        (geometricFrobeniusEquiv F E f Φ) :=
  rationalLFactor_standalonePair F E f A Φ.val

/-- The regular spectral domains agree at the same complex coordinate. -/
def spectralRegularPointEquiv
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)}) :
    WeilDeligne.SpectralRegularPoint (standalonePair F E f A) (localInertia E) Φ.val
      (E.canonicalTopologicalData.residueCardinality : ℝ)
      (standalone_residueCardinality_pos E) ≃
    SpectralRegularPoint F (extensionFiniteIntermediate F E f) A
      (geometricFrobeniusEquiv F E f Φ) where
  toFun s := ⟨s.val, by
    change (WeilDeligne.eulerPolynomial A (inertia F (extensionFiniteIntermediate F E f))
      (extensionImageWeilEquiv F E f Φ.val)).eval
        (spectralParameter (residueCardinality F (extensionFiniteIntermediate F E f))
          (residueCardinality_pos F (extensionFiniteIntermediate F E f)) s.val : ℂ) ≠ 0
    rw [spectralParameter_eq, ← eulerPolynomial_standalonePair]
    exact s.property⟩
  invFun s := ⟨s.val, by
    change (WeilDeligne.eulerPolynomial (standalonePair F E f A) (localInertia E) Φ.val).eval
      (spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
        (standalone_residueCardinality_pos E) s.val : ℂ) ≠ 0
    rw [eulerPolynomial_standalonePair, ← spectralParameter_eq F E f]
    exact s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem spectralRegularPointEquiv_val
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)})
    (s : WeilDeligne.SpectralRegularPoint (standalonePair F E f A) (localInertia E) Φ.val
      (E.canonicalTopologicalData.residueCardinality : ℝ)
      (standalone_residueCardinality_pos E)) :
    (spectralRegularPointEquiv F E f A Φ s).val = s.val := rfl

/-- Equality of actual unit-valued reciprocal evaluations on their regular domains. -/
theorem spectralLValue_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)})
    (s : WeilDeligne.SpectralRegularPoint (standalonePair F E f A) (localInertia E) Φ.val
      (E.canonicalTopologicalData.residueCardinality : ℝ)
      (standalone_residueCardinality_pos E)) :
    WeilDeligne.spectralLValue (standalonePair F E f A) (localInertia E) Φ.val
      (E.canonicalTopologicalData.residueCardinality : ℝ)
      (standalone_residueCardinality_pos E) s =
    spectralLValue F (extensionFiniteIntermediate F E f) A
      (geometricFrobeniusEquiv F E f Φ) (spectralRegularPointEquiv F E f A Φ s) := by
  apply Units.ext
  change ((WeilDeligne.eulerPolynomial (standalonePair F E f A) (localInertia E) Φ.val).eval
    (spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
      (standalone_residueCardinality_pos E) s.val : ℂ))⁻¹ =
    ((WeilDeligne.eulerPolynomial A (inertia F (extensionFiniteIntermediate F E f))
      (extensionImageWeilEquiv F E f Φ.val)).eval
        (spectralParameter (residueCardinality F (extensionFiniteIntermediate F E f))
          (residueCardinality_pos F (extensionFiniteIntermediate F E f)) s.val : ℂ))⁻¹
  rw [eulerPolynomial_standalonePair, spectralParameter_eq]

/-- The actual quotient determinant correction agrees at every spectral coordinate. -/
theorem quotientValue_standalonePair
    (A : Pair.{uF, uV} F (extensionFiniteIntermediate F E f))
    (Φ : {w : localWeilGroup E // localDegree E w = Multiplicative.ofAdd (1 : ℤ)})
    (s : ℂ) :
    WeilDeligne.quotientCorrectionValue (standalonePair F E f A) (localInertia E) Φ.val
      (spectralParameter (E.canonicalTopologicalData.residueCardinality : ℝ)
        (standalone_residueCardinality_pos E) s) =
    quotientValue F (extensionFiniteIntermediate F E f) A
      (geometricFrobeniusEquiv F E f Φ) s := by
  unfold quotientValue
  rw [quotientCorrectionValue_standalonePair, spectralParameter_eq]
  rfl

end Langlands.LocalFactor.CommonClosureWeilDeligne.Transport
