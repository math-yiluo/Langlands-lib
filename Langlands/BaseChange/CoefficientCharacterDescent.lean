import Langlands.BaseChange.CharacterFunction
import Langlands.BaseChange.EllipticCharacterCentralProduct
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.ShintaniCentralCharacter

/-! # The product of a regular character and a conjugate coefficient on `GL_n/Z` -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory JacquetLanglands

universe u uV uW

variable {F : Type u} [Field F] {n : ℕ}

local notation "G" => GeneralLinear n F
local notation "Z" => Subgroup.center G

/-- The values of `Θ` on the regular semisimple set, extended by zero. -/
def regularCharacterExtension (Θ : G → ℂ) : G → ℂ :=
  {g : G | IsRegularSemisimple g}.indicator Θ

private theorem regularSemisimple_center_mul (z : Z) {g : G} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple ((z : G) * g) := by
  have hz : (z : G) ∈ (GeneralLinear.scalar (n := n)).range := by
    simpa only [GeneralLinear.scalar, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
      using z.property
  obtain ⟨a, ha⟩ := hz
  rw [← ha]
  exact isRegularSemisimple_scalar_mul hg a

private theorem regularSemisimple_center_mul_iff (z : Z) (g : G) :
    IsRegularSemisimple ((z : G) * g) ↔ IsRegularSemisimple g :=
  ⟨fun h => by simpa using regularSemisimple_center_mul z⁻¹ h,
    regularSemisimple_center_mul z⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GeneralLinear n F) V}
  {π : Representation ℂ (GeneralLinear n F) W} {hρ : IsAdmissible ρ}

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace

/-- Zero extension off the regular semisimple locus preserves the character density,
since that locus is Haar conull. -/
theorem IsCharacterFunction.regularCharacterExtension {Θ : G → ℂ}
    (hΘ : IsCharacterFunction ρ hρ Θ) :
    IsCharacterFunction ρ hρ (regularCharacterExtension Θ) := by
  apply hΘ.congr_ae
  intro ν _
  have hreg : ∀ᵐ g ∂ν, IsRegularSemisimple g :=
    ae_iff.mpr ((regularSemisimpleOpenConull F n).2 ν)
  filter_upwards [hreg] with g hg
  exact (Set.indicator_of_mem (s := {g : G | IsRegularSemisimple g}) hg Θ).symm

private theorem regularCharacterExtension_center_mul (cρ : UnitaryCentralCharacter ρ)
    (Θ : G → ℂ) (hΘ : ∀ g, IsRegularSemisimple g → HasCharacterValue ρ hρ g (Θ g))
    (z : Z) (g : G) :
    regularCharacterExtension Θ ((z : G) * g) =
      (cρ.character z : ℂ) * regularCharacterExtension Θ g := by
  by_cases hg : IsRegularSemisimple g
  · have hzg := regularSemisimple_center_mul z hg
    simpa only [regularCharacterExtension, Set.indicator_of_mem
      (s := {g : G | IsRegularSemisimple g}) hzg, Set.indicator_of_mem
      (s := {g : G | IsRegularSemisimple g}) hg] using
      (hΘ _ hzg).unique (hasCharacterValue_mul_left_of_scalar (hΘ _ hg) (cρ.acts z))
  · have hzg : ¬ IsRegularSemisimple ((z : G) * g) :=
      fun h => hg ((regularSemisimple_center_mul_iff z g).mp h)
    simp [regularCharacterExtension, hg, hzg]

private theorem characterCoefficient_center_mul (cρ : UnitaryCentralCharacter ρ)
    (cπ : UnitaryCentralCharacter π) (hc : cρ.character = cπ.character)
    (Θ : G → ℂ) (hΘ : ∀ g, IsRegularSemisimple g → HasCharacterValue ρ hρ g (Θ g))
    (v : W) (ℓ : SmoothDual π) (z : Z) (g : G) :
    regularCharacterExtension Θ ((z : G) * g) * star (ℓ.val (π ((z : G) * g) v)) =
      regularCharacterExtension Θ g * star (ℓ.val (π g v)) := by
  rw [regularCharacterExtension_center_mul cρ Θ hΘ z g, hc, map_mul,
    Module.End.mul_apply, cπ.acts z, map_smul, smul_eq_mul, star_mul]
  let a : ℂ := cπ.character z
  have ha : a * star a = 1 := by
    change a * (starRingEnd ℂ) a = 1
    rw [← Complex.inv_eq_conj (cπ.norm_eq_one z), mul_inv_cancel₀ (cπ.character z).ne_zero]
  calc
    _ = (a * star a) * (regularCharacterExtension Θ g * star (ℓ.val (π g v))) := by
      change (a * regularCharacterExtension Θ g) * (star (ℓ.val (π g v)) * star a) = _
      ring
    _ = _ := by rw [ha, one_mul]

/-- Multiply the regular character of `ρ` by the conjugate coefficient of `π`
and descend the product to `GL_n/Z`. The representations have a common unitary
central character, and the character factor is zero off the regular locus. -/
def characterCoefficientProduct (cρ : UnitaryCentralCharacter ρ)
    (cπ : UnitaryCentralCharacter π) (hc : cρ.character = cπ.character)
    (Θ : G → ℂ) (hΘ : ∀ g, IsRegularSemisimple g → HasCharacterValue ρ hρ g (Θ g))
    (v : W) (ℓ : SmoothDual π) : G ⧸ Z → ℂ :=
  Quotient.lift (fun g => regularCharacterExtension Θ g * star (ℓ.val (π g v))) (by
    intro x y hxy
    let z : Z := ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp hxy⟩
    have hy : (z : G) * x = y := by
      rw [← Subgroup.mem_center_iff.mp z.property x]
      simp [z]
    rw [← hy, characterCoefficient_center_mul cρ cπ hc Θ hΘ v ℓ])

theorem characterCoefficientProduct_mk (cρ : UnitaryCentralCharacter ρ)
    (cπ : UnitaryCentralCharacter π) (hc : cρ.character = cπ.character)
    (Θ : G → ℂ) (hΘ : ∀ g, IsRegularSemisimple g → HasCharacterValue ρ hρ g (Θ g))
    (v : W) (ℓ : SmoothDual π) (g : G) :
    characterCoefficientProduct cρ cπ hc Θ hΘ v ℓ (QuotientGroup.mk g) =
      regularCharacterExtension Θ g * star (ℓ.val (π g v)) :=
  rfl

end Langlands.BaseChange
