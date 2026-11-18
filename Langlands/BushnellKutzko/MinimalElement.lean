import Langlands.BushnellKutzko.SubfieldIntegers

/-! # Minimal elements (BK93 (1.4.14), printed p. 41)

The normalized valuation and reduction are constructed from the already published integral
closure `subfieldIntegers F E`, without requiring a supplied valuation on `E`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE

variable (F : Type uF) [Field F] [ValuativeRel F]
  (E : Type uE) [Field E] [Algebra F E]

/-- The residue ring `𝔬_E/𝔭_E`, from the published integral closure and its
Jacobson radical. For finite extensions of local fields this is `k_E`. -/
abbrev subfieldResidueRing :=
  (subfieldIntegers F E) ⧸ subfieldMaximalIdeal F E

open scoped Classical in
/-- The normalized additive valuation on `E`, constructed from `𝔬_E`.
For `x ≠ 0` it is the integer exponent in a representation `x = π^n u`,
where `π` generates `𝔭_E` and `u ∈ 𝔬_Eˣ`; it is `∞` at zero.
The integer supremum makes the definition total outside the finite-local-field setting. -/
def subfieldNormalizedValuation (x : E) : WithTop ℤ :=
  if x = 0 then ⊤ else
    ((sSup {n : ℤ | ∃ π : subfieldIntegers F E,
      π ≠ 0 ∧ Ideal.span ({π} : Set (subfieldIntegers F E)) = subfieldMaximalIdeal F E ∧
      ∃ u : (subfieldIntegers F E)ˣ,
        x = (π : E) ^ n * ((u : subfieldIntegers F E) : E)} : ℤ) : WithTop ℤ)

/-- Minimality over `F` for a generator `β` of the field extension `E/F`
(BK93 (1.4.14), p. 41). Residue generation is expressed over `𝔬_F`,
whose image in `k_E` is the base residue field `k_F`. -/
def IsMinimalOver (β : E) : Prop :=
  Algebra.adjoin F ({β} : Set E) = ⊤ ∧
  ∃ ν : ℤ, subfieldNormalizedValuation F E β = (ν : WithTop ℤ) ∧
    Nat.Coprime ν.natAbs (subfieldRamificationIndex F E) ∧
    ∃ π : 𝒪[F], π ≠ 0 ∧ Ideal.span ({π} : Set 𝒪[F]) = 𝓂[F] ∧
      ∃ y : subfieldIntegers F E,
        (y : E) = algebraMap F E (π : F) ^ (-ν) * β ^ subfieldRamificationIndex F E ∧
        Algebra.adjoin 𝒪[F]
          ({Ideal.Quotient.mk (subfieldMaximalIdeal F E) y} :
            Set (subfieldResidueRing F E)) = ⊤

end Langlands.BushnellKutzko
