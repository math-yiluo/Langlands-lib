import Langlands.Representation.RankinSelberg.HighlyRamified.DualSmear
import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly

/-!
# The twisted smeared second dual is a model function

Let `σ` be a generic representation of `GL_(m+2)` with a nonzero functional `ℓ'` for the
inverse standard character, and let `f'` be a function of the model of `(σ, ℓ')`. For a
continuous character `χ` and a locally constant compactly supported weight `S` on the row
space, the function
`g ↦ χ(det g)⁻¹ ∫ S(x) f̃'(g ū_x) dx`
(with `f̃'` the second dual function of `f'`) is a model function of the twist
`(χ⁻¹ ∘ det) ⊗ σ^ι` of the inverse transpose, for a nonzero standard-character functional,
and it is right invariant under an open subgroup. This twisted inverse transpose is generic
for `ψ`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance twistedSmearFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance twistedSmearValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance twistedSmearLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance twistedSmearSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance twistedSmearFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance twistedSmearFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {m : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  {W : Type uV} [AddCommGroup W] [Module ℂ W]

/-- The standard-character functional of the inverse transpose obtained from a functional
for the inverse character: the second dual functional, read for `ψ`. -/
def inverseTransposeFunctional {n : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ℓ : Whittaker.glInverseFunctionals ψ n σ) :
    Whittaker.glFunctionals ψ n (inverseTransposePullback σ) :=
  functionalsCongr (inverseStandardCharacter_scale_neg_one ψ n) (secondDualFunctional ψ σ ℓ)

/-- The inverse transpose of a `ψ`-generic representation with a nonzero functional for the
inverse character is again `ψ`-generic. -/
theorem isGeneric_inverseTransposePullback_of_inverse {n : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hσ : Whittaker.IsGeneric ψ n σ) (ℓ : Whittaker.glInverseFunctionals ψ n σ)
    (hℓ : ℓ.val ≠ 0) :
    Whittaker.IsGeneric ψ n (inverseTransposePullback σ) := by
  obtain ⟨h1, h2, -⟩ := isGeneric_inverseTransposePullback F ψ σ hσ
  exact ⟨h1, h2, inverseTransposeFunctional F ψ σ ℓ, secondDualFunctional_ne_zero ψ σ hℓ⟩

/-- The continuous character `χ⁻¹` as a quasicharacter. -/
def inverseQuasicharacter (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) :
    Quasicharacter F.Carrier :=
  ⟨χ⁻¹, hχ.inv⟩

/-- The twist of the inverse transpose by `χ⁻¹ ∘ det` is `ψ`-generic. -/
theorem isGeneric_twist_inverseTransposePullback
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) W)
    (hσ : Whittaker.IsGeneric ψ (m + 1) σ) (ℓ' : Whittaker.glInverseFunctionals ψ (m + 1) σ)
    (hℓ' : ℓ'.val ≠ 0) (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) :
    Whittaker.IsGeneric ψ (m + 1)
      (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback σ)) :=
  isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ (inverseQuasicharacter F χ hχ)
    (isGeneric_inverseTransposePullback_of_inverse F ψ σ hσ ℓ' hℓ')

/-- The product Haar measure on the row space is finite on compact sets. -/
theorem rectangularMeasure_isFiniteMeasureOnCompacts (η : AdditiveHaarMeasure F.Carrier)
    (j t : ℕ) : IsFiniteMeasureOnCompacts (rectangularMeasure η j t) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts
    (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => η.measure))))

/-- The twisted smeared second dual `g ↦ χ(det g)⁻¹ ∫ S(x) f̃'(g ū_x) dx` is a function of the
model of `(χ⁻¹ ∘ det) ⊗ σ^ι` for a nonzero standard-character functional, and it is right
invariant under an open subgroup. -/
theorem exists_twistedSmear_model (η : AdditiveHaarMeasure F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) W)
    (hσ : Whittaker.IsGeneric ψ (m + 1) σ) (ℓ' : Whittaker.glInverseFunctionals ψ (m + 1) σ)
    (hℓ' : ℓ'.val ≠ 0) (f' : (Whittaker.coefficientModel σ ℓ').toSubmodule)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ)
    (S : Matrix (Fin 1) (Fin (m + 1)) F.Carrier → ℂ) (hS : IsLocallyConstant S)
    (hSc : HasCompactSupport S) :
    ∃ ℓF : Whittaker.glFunctionals ψ (m + 1)
        (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback σ)),
      ℓF.val ≠ 0 ∧
      ∃ Fbig : (Whittaker.coefficientModel
          (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback σ))
          ℓF).toSubmodule,
        (∀ g, Fbig.val.val g = ((χ (determinant g) : ℂ))⁻¹ *
          ∫ x, S x * (secondDualFunction ψ (m + 1) f'.val).val (g * lowerRow x)
            ∂rectangularMeasure η 1 (m + 1)) ∧
        ∃ L : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier),
          ∀ g l, l ∈ L → Fbig.val.val (g * l) = Fbig.val.val g := by
  have := rectangularMeasure_isFiniteMeasureOnCompacts F η 1 (m + 1)
  have hgen := isGeneric_inverseTransposePullback F ψ σ hσ
  have hgenT := isGeneric_twist_inverseTransposePullback F ψ σ hσ ℓ' hℓ' χ hχ
  let ℓF : Whittaker.glFunctionals ψ (m + 1)
      (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback σ)) :=
    Whittaker.twistFunctional _ _ ((χ⁻¹).comp determinant)
      (Whittaker.determinantCharacter_unipotent χ⁻¹) (inverseTransposePullback σ)
      (inverseTransposeFunctional F ψ σ ℓ')
  obtain ⟨v, hv⟩ := f'.property
  let w : W := lowerRowSmear (rectangularMeasure η 1 (m + 1)) (inverseTransposePullback σ)
    hgen.2.1.1 S hS hSc v
  let Fbig : (Whittaker.coefficientModel
      (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback σ)) ℓF).toSubmodule :=
    ⟨Whittaker.coefficientMap _ ℓF w, w, rfl⟩
  have hFbig : ∀ g, Fbig.val.val g = (secondDualFunctional ψ σ ℓ').val
      ((((χ⁻¹).comp determinant g : ℂˣ) : ℂ) • inverseTransposePullback σ g w) := fun _ => rfl
  have hsd : ∀ h, (secondDualFunction ψ (m + 1) f'.val).val h =
      (secondDualFunctional ψ σ ℓ').val (inverseTransposePullback σ h v) := by
    intro h
    rw [← hv]
    exact congrArg (fun φ : InverseWhittakerFunctions (ψ.scale (-1)) (m + 1) => φ.val h)
      (secondDualFunction_coefficient ψ σ ℓ' v)
  refine ⟨ℓF, secondDualFunctional_ne_zero ψ σ hℓ', Fbig, fun g => ?_, ?_⟩
  · rw [hFbig, map_smul, smul_eq_mul]
    congr 1
    · change (((χ (determinant g))⁻¹ : ℂˣ) : ℂ) = _
      exact Units.val_inv_eq_inv_val _
    · have h := lowerRowSmear_dual (rectangularMeasure η 1 (m + 1)) (inverseTransposePullback σ)
        hgen.2.1.1 S hS hSc v
        ((secondDualFunctional ψ σ ℓ').val ∘ₗ inverseTransposePullback σ g)
      refine h.trans ?_
      congr 1
      funext x
      rw [hsd, map_mul]
      rfl
  · obtain ⟨K, hK⟩ := hgenT.2.1.1 w
    refine ⟨K, fun g l hl => ?_⟩
    change ℓF.val (Langlands.twist ((χ⁻¹).comp determinant) (inverseTransposePullback σ)
        (g * l) w) = ℓF.val (Langlands.twist ((χ⁻¹).comp determinant)
          (inverseTransposePullback σ) g w)
    rw [map_mul, Module.End.mul_apply]
    exact congrArg (fun u => ℓF.val (Langlands.twist ((χ⁻¹).comp determinant)
      (inverseTransposePullback σ) g u)) (hK ⟨l, hl⟩)

end Langlands.RankinSelberg.HighlyRamified
