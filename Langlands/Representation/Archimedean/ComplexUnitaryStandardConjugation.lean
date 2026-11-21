import Langlands.Representation.Archimedean.ComplexBlockRestriction
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.Representation.Archimedean.ComplexStandardOppositeOrderHomReduction
import Langlands.LocalFactor.ArchimedeanPairFactor

/-! Pointwise conjugation and the Hermitian-dual parameters of a complex principal series. -/

noncomputable section

open scoped ComplexConjugate ContDiff Manifold Matrix TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

open Langlands.LocalFactor.Archimedean

/-- Conjugation of the value of a character, with weight `-m` and exponent `conj t`. -/
def conjugateData (d : ComplexCharacterData) : ComplexCharacterData where
  character := complexConjugation.comp d.character
  weight := -d.weight
  exponent := conj d.exponent
  character_eq z := by
    change conj (d.character z : ℂ) = _
    have harg : ((‖(z : ℂ)‖ : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (norm_nonneg _)]
      exact Real.pi_ne_zero.symm
    have hphase : conj ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) =
        ((z : ℂ) / (‖(z : ℂ)‖ : ℂ))⁻¹ :=
      (Complex.inv_eq_conj (ComplexGramFormula.norm_phaseUnit z)).symm
    have hpow : conj ((‖(z : ℂ)‖ : ℂ) ^ (2 * d.exponent)) =
        (‖(z : ℂ)‖ : ℂ) ^ conj (2 * d.exponent) := by
      simpa only [Complex.conj_ofReal] using (Complex.cpow_conj _ (2 * d.exponent) harg).symm
    have htwo : conj (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
    rw [d.character_eq, map_mul, map_zpow₀, hphase, inv_zpow', zpow_neg, hpow, map_mul, htwo]

/-- The Hermitian dual of a parameter of weight `m` and exponent `t` has weight `m`
and exponent `-conj t`. -/
def hermitianData (d : ComplexCharacterData) : ComplexCharacterData :=
  complexCharacterDataInv (conjugateData d)

@[simp] theorem hermitianData_weight (d : ComplexCharacterData) :
    (hermitianData d).weight = d.weight := neg_neg _

@[simp] theorem hermitianData_re (d : ComplexCharacterData) :
    (hermitianData d).exponent.re = -d.exponent.re := rfl

@[simp] theorem hermitianData_im (d : ComplexCharacterData) :
    (hermitianData d).exponent.im = d.exponent.im := neg_neg _

@[simp] theorem hermitianData_involutive (d : ComplexCharacterData) :
    hermitianData (hermitianData d) = d := by
  apply complexCharacterData_eq_of_weight_exponent
  · simp
  · apply Complex.ext <;> simp

@[simp] theorem hermitianData_eq_self_iff (d : ComplexCharacterData) :
    hermitianData d = d ↔ d.exponent.re = 0 := by
  constructor
  · intro h
    have := congrArg (fun d : ComplexCharacterData => d.exponent.re) h
    simp only [hermitianData_re] at this
    linarith
  · intro h
    apply complexCharacterData_eq_of_weight_exponent
    · simp
    · apply Complex.ext <;> simp [h]

@[simp] theorem complexPositionCharacter_map_conjugate :
    ∀ (ds : List ComplexCharacterData) (i : ℕ) (z : ℂˣ),
      complexPositionCharacter (ds.map conjugateData) i z = conj (complexPositionCharacter ds i z)
  | [], _, _ => by simp [complexPositionCharacter]
  | _ :: _, 0, _ => rfl
  | _ :: ds, i + 1, z => complexPositionCharacter_map_conjugate ds i z

variable {n : ℕ}

private def conjugateFunctions (n : ℕ) : (Langlands.GeneralLinear n ℂ → ℂ) →ₛₗ[starRingEnd ℂ]
    (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun f g := conj (f g)
  map_add' f g := by funext x; exact map_add (starRingEnd ℂ) (f x) (g x)
  map_smul' c f := by funext x; exact map_mul (starRingEnd ℂ) c (f x)

private theorem conjugateFunctions_mem_kFiniteVectors {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n)) :
    conjugateFunctions n f ∈ kFiniteVectors
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)) (unitaryCompact ℂ n) := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  have e : (Set.range fun k : unitaryCompact ℂ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (k : Langlands.GeneralLinear n ℂ) (conjugateFunctions n f)) =
      conjugateFunctions n '' Set.range fun k : unitaryCompact ℂ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
          (k : Langlands.GeneralLinear n ℂ) f := by
    rw [← Set.range_comp]
    rfl
  rw [e, ← Submodule.map_span]
  exact (Submodule.fg_iff_finiteDimensional _).mp
    (((Submodule.fg_iff_finiteDimensional _).mpr hf).map (conjugateFunctions n))

private theorem principalSeriesCharacter_conj {χ ψ : ℕ → ℂˣ → ℂ}
    (hψ : ∀ i z, ψ i z = conj (χ i z)) (a : Fin n → ℂˣ) :
    conj (principalSeriesCharacter ℂ n χ a) = principalSeriesCharacter ℂ n ψ a := by
  unfold principalSeriesCharacter
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have harg : (((‖(a i : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact Real.pi_ne_zero.symm
  let s : ℂ := ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)
  have htwo : conj (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
  have hs : conj s = s := by simp [s, htwo]
  have hpow : conj (((‖(a i : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ) : ℂ) ^ s) =
      ((‖(a i : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ) : ℂ) ^ s := by
    simpa only [Complex.conj_ofReal, hs] using (Complex.cpow_conj _ s harg).symm
  rw [map_mul, hψ]
  change _ * conj (_ ^ s) = _ * _ ^ s
  rw [hpow]

private def conjugateStandardOf (ds cs : List ComplexCharacterData)
    (hcs : ∀ i z, complexPositionCharacter cs i z = conj (complexPositionCharacter ds i z)) :
    ComplexBlock.KFs n ds →ₛₗ[starRingEnd ℂ] ComplexBlock.KFs n cs where
  toFun f := ⟨conjugateFunctions n f.1, ⟨⟨ComplexTemperedComplement.contMDiff_conj f.2.1.1,
    fun a u g => by
      change conj (f.1 _) = _ * conj (f.1 g)
      rw [f.2.1.2 a u g, map_mul, principalSeriesCharacter_conj hcs]⟩,
    conjugateFunctions_mem_kFiniteVectors f.2.2⟩⟩
  map_add' f g := Subtype.ext (map_add (conjugateFunctions n) f.1 g.1)
  map_smul' c f := Subtype.ext (map_smulₛₗ (conjugateFunctions n) c f.1)

/-- Pointwise conjugation takes the principal series to the conjugate inducing characters. -/
def conjugateStandard (ds : List ComplexCharacterData) :
    ComplexBlock.KFs n ds →ₛₗ[starRingEnd ℂ] ComplexBlock.KFs n (ds.map conjugateData) :=
  conjugateStandardOf ds _ (complexPositionCharacter_map_conjugate ds)

/-- Pointwise conjugation takes the conjugate principal series back to the original one. -/
def fromConjugateStandard (ds : List ComplexCharacterData) :
    ComplexBlock.KFs n (ds.map conjugateData) →ₛₗ[starRingEnd ℂ] ComplexBlock.KFs n ds :=
  conjugateStandardOf _ ds fun i z => by simp

@[simp] theorem conjugateStandard_apply (ds : List ComplexCharacterData) (f : ComplexBlock.KFs n ds)
    (g : Langlands.GeneralLinear n ℂ) : (conjugateStandard ds f).1 g = conj (f.1 g) := rfl

@[simp] theorem fromConjugateStandard_apply (ds : List ComplexCharacterData)
    (f : ComplexBlock.KFs n (ds.map conjugateData)) (g : Langlands.GeneralLinear n ℂ) :
    (fromConjugateStandard ds f).1 g = conj (f.1 g) := rfl

@[simp] theorem fromConjugateStandard_conjugateStandard (ds : List ComplexCharacterData)
    (f : ComplexBlock.KFs n ds) : fromConjugateStandard ds (conjugateStandard ds f) = f := by
  apply Subtype.ext
  funext g
  simp

/-- Pointwise conjugation commutes with compact right translation. -/
theorem fromConjugateStandard_rep (ds : List ComplexCharacterData)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : ComplexBlock.KFs n (ds.map conjugateData)) :
    fromConjugateStandard ds (complexStandardRep n (ds.map conjugateData) k f) =
      complexStandardRep n ds k (fromConjugateStandard ds f) := by
  apply Subtype.ext
  rw [principalSeriesRep_apply_coe]
  funext g
  change conj ((complexStandardRep n (ds.map conjugateData) k f).1 g) = _
  rw [principalSeriesRep_apply_coe]
  rfl

/-- Pointwise conjugation commutes with right differentiation in real Lie algebra directions. -/
theorem fromConjugateStandard_lie (ds : List ComplexCharacterData)
    (X : Matrix (Fin n) (Fin n) ℂ) (f : ComplexBlock.KFs n (ds.map conjugateData)) :
    fromConjugateStandard ds (complexStandardLie n (ds.map conjugateData) (1 ⊗ₜ X) f) =
      complexStandardLie n ds (1 ⊗ₜ X) (fromConjugateStandard ds f) := by
  apply Subtype.ext
  rw [principalSeriesLie_one_tmul_apply_coe]
  funext g
  change conj ((complexStandardLie n (ds.map conjugateData) (1 ⊗ₜ X) f).1 g) = _
  rw [principalSeriesLie_one_tmul_apply_coe]
  exact (ComplexTemperedComplement.rightDerivative_conj f.2.1.1 X g).symm

end Langlands.Archimedean.ComplexUnitary
