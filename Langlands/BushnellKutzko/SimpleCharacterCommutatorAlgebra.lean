import Langlands.BushnellKutzko.SimpleCharacterCentralizer
import Langlands.BushnellKutzko.SimpleCharacterCovarianceStatement
import Langlands.BushnellKutzko.CharacterNormalizerSubgroup
import Langlands.BushnellKutzko.CharacterCommutatorDepth

/-! # Factorizations used to calculate character commutators -/

noncomputable section

open ValuativeRel
open scoped commutatorElement Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- A character evaluated at a commutator is the trace factor of the
conjugation difference, with membership in the domain included. -/
def characterCommutatorFormula (ψF : AddChar F ℂ) (b : A) {H : Subgroup G}
    (θ : H →* ℂˣ) (x y : G) : Prop :=
  ∃ hc : ⁅x, y⁆ ∈ H, (θ ⟨_, hc⟩ : ℂ) =
    elementCharacter (traceCharacter ψF) ((↑x⁻¹ : A) * b * (x : A) - b) y

private theorem conjugationDifference_eq_zero_of_centralizer {b : A} {x : G}
    (hx : x ∈ centralizerUnitGroup b) : (↑x⁻¹ : A) * b * (x : A) - b = 0 := by
  have h : b * (x : A) = (x : A) * b := hx
  rw [mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul, sub_self]

/-- If two units centralize the parameter, the character of their commutator
is trivial whenever it belongs to the determinant-factorizing domain. -/
theorem factorsThroughCentralizerDet.commutator_eq_one {b : A} {H : Subgroup G} {θ : H →* ℂˣ}
    (hθ : factorsThroughCentralizerDet b θ) {x y : G}
    (hx : x ∈ centralizerUnitGroup b) (hy : y ∈ centralizerUnitGroup b)
    (hxy : ⁅x, y⁆ ∈ H) : θ ⟨_, hxy⟩ = 1 := by
  obtain ⟨hE, hθ⟩ := hθ
  let := hE.toField
  let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra b)
  let e := relativeEndUnitEquiv b hE
  let u := e.symm ⟨x, hx⟩
  let v := e.symm ⟨y, hy⟩
  have hu : ι u = x := congrArg (fun z : centralizerUnitGroup b => (z : G)) (e.apply_symm_apply _)
  have hv : ι v = y := congrArg (fun z : centralizerUnitGroup b => (z : G)) (e.apply_symm_apply _)
  have heq : ι ⁅u, v⁆ = ⁅x, y⁆ := by simp only [commutatorElement_def, map_mul, map_inv, hu, hv]
  let d : (Module.End (elementAlgebra b) V)ˣ →* (elementAlgebra b)ˣ := Units.map LinearMap.det
  let z : H.comap ι := ⟨⁅u, v⁆, show ι ⁅u, v⁆ ∈ H from heq.symm ▸ hxy⟩
  let f := d.comp (H.comap ι).subtype
  obtain ⟨η, hη⟩ := hθ
  have hd : f.rangeRestrict z = 1 := by
    apply Subtype.ext
    change d ⁅u, v⁆ = 1
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc
      d u * d v * (d u)⁻¹ * (d v)⁻¹ = (d u * (d u)⁻¹) * (d v * (d v)⁻¹) := by ac_rfl
      _ = 1 := by simp only [mul_inv_cancel, mul_one]
  calc
    θ ⟨_, hxy⟩ = θ ⟨ι z, z.property⟩ := congrArg θ (Subtype.ext heq.symm)
    _ = η (f.rangeRestrict z) := hη z
    _ = 1 := by rw [hd, map_one]

/-- The determinant calculation gives the trace formula for two relative units. -/
theorem characterCommutatorFormula.of_centralizer (ψF : AddChar F ℂ) {b : A} {H : Subgroup G}
    {θ : H →* ℂˣ} (hθ : factorsThroughCentralizerDet b θ) {x y : G}
    (hx : x ∈ centralizerUnitGroup b) (hy : y ∈ centralizerUnitGroup b) (hxy : ⁅x, y⁆ ∈ H) :
    characterCommutatorFormula ψF b θ x y := by
  refine ⟨hxy, ?_⟩
  rw [hθ.commutator_eq_one hx hy hxy, conjugationDifference_eq_zero_of_centralizer hx]
  simp [elementCharacter_apply]

/-- Left factorization of the first unit when the first factor centralizes the
parameter and normalizes the character. -/
theorem characterCommutatorFormula.mul_left_of_centralizer (ψF : AddChar F ℂ)
    {b : A} {H : Subgroup G} {θ : H →* ℂˣ} {x₁ x₂ y : G}
    (h₁ : characterCommutatorFormula ψF b θ x₁ y) (h₂ : characterCommutatorFormula ψF b θ x₂ y)
    (hx₁ : x₁ ∈ centralizerUnitGroup b) (hn : x₁ ∈ characterNormalizerSubgroup θ) :
    characterCommutatorFormula ψF b θ (x₁ * x₂) y := by
  obtain ⟨hc₁, h₁⟩ := h₁
  obtain ⟨hc₂, h₂⟩ := h₂
  have hN : x₁ ∈ characterNormalizer θ := hn
  let u : H := ⟨_, hc₂⟩
  have hu := (Subgroup.mem_normalizer_iff.mp hN.1 (u : G)).mp u.property
  let v : H := ⟨_, hu⟩
  let w : H := v * ⟨_, hc₁⟩
  have hw : (w : G) = ⁅x₁ * x₂, y⁆ := (commutatorElement_mul_left_eq_conj_mul x₁ x₂ y).symm
  have hw' : ⁅x₁ * x₂, y⁆ ∈ H := hw ▸ w.property
  have hdiff : (↑(x₁ * x₂)⁻¹ : A) * b * (↑(x₁ * x₂) : A) - b =
      (↑x₂⁻¹ : A) * b * (x₂ : A) - b := by
    have he : (↑x₁⁻¹ : A) * b * (x₁ : A) = b :=
      sub_eq_zero.mp (conjugationDifference_eq_zero_of_centralizer hx₁)
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    rw [show (↑x₂⁻¹ : A) * (↑x₁⁻¹ : A) * b * ((x₁ : A) * (x₂ : A)) =
      (↑x₂⁻¹ : A) * ((↑x₁⁻¹ : A) * b * (x₁ : A)) * (x₂ : A) by simp only [mul_assoc], he]
  have hval : θ v = θ u := hN.2 u hu
  rw [conjugationDifference_eq_zero_of_centralizer hx₁] at h₁
  refine ⟨hw', ?_⟩
  rw [show (⟨_, hw'⟩ : H) = w from Subtype.ext hw.symm, hdiff]
  change (θ (v * ⟨_, hc₁⟩) : ℂ) = _
  rw [map_mul, Units.val_mul, hval, h₂, h₁]
  simp [elementCharacter_apply]

/-- The commutator formulas for the two factors of the second unit combine
when the first factor normalizes the character and the trace character
of the cross term is one. -/
theorem characterCommutatorFormula.mul_right (ψF : AddChar F ℂ) {b : A} {H : Subgroup G}
    {θ : H →* ℂˣ} {x y₁ y₂ : G}
    (h₁ : characterCommutatorFormula ψF b θ x y₁) (h₂ : characterCommutatorFormula ψF b θ x y₂)
    (hn : y₁ ∈ characterNormalizerSubgroup θ)
    (htrace : traceCharacter ψF (((↑x⁻¹ : A) * b * (x : A) - b) *
        (((y₁ : A) - 1) * ((y₂ : A) - 1))) = 1) :
    characterCommutatorFormula ψF b θ x (y₁ * y₂) := by
  obtain ⟨hc₁, h₁⟩ := h₁
  obtain ⟨hc₂, h₂⟩ := h₂
  have hN : y₁ ∈ characterNormalizer θ := hn
  let u : H := ⟨_, hc₂⟩
  have hu := (Subgroup.mem_normalizer_iff.mp hN.1 (u : G)).mp u.property
  let v : H := ⟨_, hu⟩
  let w : H := ⟨_, hc₁⟩ * v
  have hw : (w : G) = ⁅x, y₁ * y₂⁆ := (commutatorElement_mul_right_eq_mul_conj x y₁ y₂).symm
  have hw' : ⁅x, y₁ * y₂⁆ ∈ H := hw ▸ w.property
  let d := (↑x⁻¹ : A) * b * (x : A) - b
  have hprod : d * ((↑(y₁ * y₂) : A) - 1) =
      (d * ((y₁ : A) - 1) + d * ((y₂ : A) - 1)) + d * (((y₁ : A) - 1) * ((y₂ : A) - 1)) := by
    rw [Units.val_mul]
    noncomm_ring
  have hval : θ v = θ u := hN.2 u hu
  refine ⟨hw', ?_⟩
  rw [show (⟨_, hw'⟩ : H) = w from Subtype.ext hw.symm]
  change (θ (⟨_, hc₁⟩ * v) : ℂ) = elementCharacter (traceCharacter ψF) d (y₁ * y₂)
  rw [map_mul, Units.val_mul, hval, h₁, h₂]
  simp only [elementCharacter_apply, hprod, AddChar.map_add_eq_mul,
    show traceCharacter ψF (d * (((y₁ : A) - 1) * ((y₂ : A) - 1))) = 1 from htrace, mul_one]
  rfl

/-- Twisting on the domain adds the coefficient of the twisting function to
the trace identity, given the additive commutator estimate for that function. -/
theorem characterCommutatorFormula.of_twist (ψF : AddChar F ℂ) {b c : A} {H : Subgroup G}
    {θ θ₀ : H →* ℂˣ} {x y : G} (h₀ : characterCommutatorFormula ψF b θ₀ x y)
    (htwist : ∀ h : H, (θ h : ℂ) = (θ₀ h : ℂ) * elementCharacter (traceCharacter ψF) c (h : G))
    (hc : elementCharacter (traceCharacter ψF) c ⁅x, y⁆ =
      elementCharacter (traceCharacter ψF) ((↑x⁻¹ : A) * c * (x : A) - c) y) :
    characterCommutatorFormula ψF (b + c) θ x y := by
  obtain ⟨hm, h₀⟩ := h₀
  refine ⟨hm, ?_⟩
  have hd : (↑x⁻¹ : A) * (b + c) * (x : A) - (b + c) =
      ((↑x⁻¹ : A) * b * (x : A) - b) + ((↑x⁻¹ : A) * c * (x : A) - c) := by noncomm_ring
  rw [htwist, h₀, hc, hd, elementCharacter_add]

variable [ValuativeRel F]

/-- An additive decomposition lifts to a product of congruence units. The inverse
of the first factor acts on the second summand. -/
theorem exists_mul_of_sub_one_mem_sup (L : LatticeChain 𝒪[F] F V)
    {U W : Submodule 𝒪[F] A} (hU : U ≤ L.endFiltration 1) (hUW : U * W ≤ W)
    (hInv : ∀ g : G, (g : A) - 1 ∈ U → (↑g⁻¹ : A) - 1 ∈ U)
    {x : G} (hx : (x : A) - 1 ∈ U ⊔ W) :
    ∃ u : G, (u : A) - 1 ∈ U ∧ ∃ w : G, (w : A) - 1 ∈ W ∧ u * w = x := by
  obtain ⟨a, ha, b, hb, hsum⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u, _, hval⟩ := L.exists_mem_unitFiltration (n := 1) (by decide) (hU ha)
  have hu : (u : A) - 1 ∈ U := by simpa only [hval, add_sub_cancel_left] using ha
  have hu' : (↑u⁻¹ : A) - 1 ∈ U := hInv u hu
  refine ⟨u, hu, u⁻¹ * x, ?_, by group⟩
  have hsub : (x : A) - (u : A) = b := by rw [hval, ← sub_sub, ← hsum, add_sub_cancel_left]
  have he : (↑(u⁻¹ * x) : A) - 1 = (↑u⁻¹ : A) * ((x : A) - (u : A)) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul]
  rw [he, hsub]
  have he' : (↑u⁻¹ : A) * b = b + ((↑u⁻¹ : A) - 1) * b := by noncomm_ring
  rw [he']
  exact add_mem hb (hUW (Submodule.mul_mem_mul hu' hb))

end Langlands.BushnellKutzko
