import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.AdelicFunctoriality.CompletedRamification

/-!
# Unramified values of norm-composed Hecke characters

An unramified local character takes one value on all elements of a given valuation. At a
place `q` of `L` above a place `p` of `K` with ramification index one, the character
`χ ∘ N_{L/K}` sends every uniformizer of `L_q` to `χ_p(ϖ) ^ f(q|p)`, where `ϖ` is any
uniformizer of `K_p`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

section Unramified

variable {K : Type u} [Field K] [NumberField K]

/-- A unit of valuation one lies in the units of the valuation ring. -/
theorem mem_units_of_valued_eq_one {p : FinitePlace K} {x : (FiniteCompletion K p)ˣ}
    (hx : Valued.v (x : FiniteCompletion K p) = 1) :
    x ∈ (Submonoid.ofClass (p.adicCompletionIntegers K)).units := by
  refine ⟨show Valued.v (x : FiniteCompletion K p) ≤ 1 from hx.le, ?_⟩
  change Valued.v ((x⁻¹ : (FiniteCompletion K p)ˣ) : FiniteCompletion K p) ≤ 1
  rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]

/-- An unramified local component takes the same value on two units of equal valuation. -/
theorem finiteComponent_eq_of_valued_eq (χ : HeckeCharacter K) {p : FinitePlace K}
    (hχ : χ.IsUnramifiedAt p) {x y : (FiniteCompletion K p)ˣ}
    (h : Valued.v (x : FiniteCompletion K p) = Valued.v (y : FiniteCompletion K p)) :
    χ.finiteComponent p x = χ.finiteComponent p y := by
  have hy : Valued.v (y : FiniteCompletion K p) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact y.ne_zero
  have hxy : Valued.v ((x * y⁻¹ : (FiniteCompletion K p)ˣ) : FiniteCompletion K p) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h, mul_inv_cancel₀ hy]
  have h1 := hχ _ (mem_units_of_valued_eq_one hxy)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Unramified

variable {K : Type u} {L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- At a place `q` above `p` with ramification index one, the component of `χ ∘ N_{L/K}` at
any uniformizer `π` of `L_q` is `χ_p(ϖ) ^ f(q|p)` for any uniformizer `ϖ` of `K_p`, when `χ`
is unramified at `p`. -/
theorem normComp_finiteComponent_uniformizer (χ : HeckeCharacter K) (p : FinitePlace K)
    (q : FinitePlacesAbove L p) (he : q.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (hχ : χ.IsUnramifiedAt p) (π : (FiniteCompletion L q.1)ˣ)
    (hπ : Valued.v (π : FiniteCompletion L q.1) = WithZero.exp (-1 : ℤ))
    (ϖ : (FiniteCompletion K p)ˣ)
    (hϖ : Valued.v (ϖ : FiniteCompletion K p) = WithZero.exp (-1 : ℤ)) :
    (normComp (L := L) χ).finiteComponent q.1 π =
      χ.finiteComponent p ϖ ^ q.1.asIdeal.inertiaDeg (𝓞 K) := by
  have : q.1.asIdeal.LiesOver p.asIdeal := q.2
  rw [normComp_finiteComponent]
  let ϖ' : (FiniteCompletion L q.1)ˣ :=
    Units.map (FiniteExtension.completionMap p q.1).toMonoidHom ϖ
  have hϖ' : Valued.v (ϖ' : FiniteCompletion L q.1) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (FiniteExtension.completionMap p q.1 (ϖ : FiniteCompletion K p)) = _
    rw [FiniteExtension.valuation_completionMap, he, pow_one, hϖ]
  let ε : (FiniteCompletion L q.1)ˣ := ϖ'⁻¹ * π
  have hε : Valued.v (ε : FiniteCompletion L q.1) = 1 := by
    have h0 : Valued.v (ϖ' : FiniteCompletion L q.1) ≠ 0 := by
      rw [hϖ']
      exact WithZero.coe_ne_zero
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ, ← hϖ',
      inv_mul_cancel₀ h0]
  have hπε : π = ϖ' * ε := by
    simp only [ε, mul_inv_cancel_left]
  have hnorm : FiniteExtension.localUnitNorm p q.1 ϖ' = ϖ ^ q.1.asIdeal.inertiaDeg (𝓞 K) := by
    apply Units.ext
    rw [FiniteExtension.localUnitNorm_val]
    change FiniteExtension.localNorm p q.1
        (FiniteExtension.completionMap p q.1 (ϖ : FiniteCompletion K p)) = _
    rw [FiniteExtension.localNorm_algebraMap, localDegree_eq, he, one_mul, Units.val_pow_eq_pow_val]
  have hunit : χ.finiteComponent p (FiniteExtension.localUnitNorm p q.1 ε) = 1 :=
    hχ _ (FiniteExtension.localUnitNorm_integral p q.1 (mem_units_of_valued_eq_one hε))
  rw [hπε, map_mul, map_mul, hnorm, hunit, mul_one, map_pow]

end Langlands.Global.HeckeCharacter
