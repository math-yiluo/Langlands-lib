import Langlands.Representation.Plancherel.RationalUnitaryRegularValue
import Langlands.Representation.Plancherel.RationalUnramifiedFactorization
import Mathlib.RingTheory.Localization.NumDen

/-! # One denominator for a fraction regular on the actual unitary group -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance scalarDenominatorPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
set_option quotPrecheck false in
local notation "ν" => fun a => (rationalNormCharacters G a).toMul
local notation "R" => unramifiedRegularFunctions ν
local notation "Xu" => unitaryUnramifiedCharacters ν

/-- The same regular fraction with a single denominator nonzero throughout
the actual unitary group. -/
structure UnitaryRegularScalarPresentation (a b : R) where
  numerator : R
  denominator : R
  nonzero : ∀ z : Xu, denominator.val (unitaryToUnramified G z) ≠ 0
  cross : b * numerator = denominator * a

namespace UnitaryRegularScalarPresentation

variable (hG : IsConnectedReductive G)

local notation "hp" => continuous_rationalValuationImageProjection G
local notation "L" => rationalUnramifiedFunctionField G hp hG

/-- Pointwise algebraic regularity on the full unitary group makes the
denominator of a reduced fraction nonzero on the full unitary group. -/
def ofUnitaryRegular (a b : R) (hb : b ≠ 0)
    (h : RationalFunctionUnitaryRegular G hG (algebraMap R L a / algebraMap R L b)) :
    UnitaryRegularScalarPresentation G a b :=
  Classical.choice (by
    let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain G hp hG
    let : UniqueFactorizationMonoid R := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid G hp hG
    let i := algebraMap R L
    have hi := rationalUnramifiedFunctionField_algebraMap_injective G hp hG
    obtain ⟨p, q, hcop, hfrac⟩ := IsFractionRing.exists_reduced_fraction R (i a / i b)
    rw [IsFractionRing.mk'_eq_div] at hfrac
    have hmap_ne_zero {d : R} (hd : d ≠ 0) : i d ≠ 0 :=
      fun h0 => hd (hi (h0.trans (map_zero i).symm))
    have hq := hmap_ne_zero (nonZeroDivisors.ne_zero q.property)
    have hcross (m n : R) (hn : n ≠ 0) (he : i a / i b = i m / i n) :
        p * n = m * (q : R) := by
      have hpn := (div_eq_div_iff hq (hmap_ne_zero hn)).mp (hfrac.trans he)
      exact hi (by simpa only [map_mul] using hpn)
    refine ⟨⟨p, q, ?_, ?_⟩⟩
    · intro z
      obtain ⟨m, n, hn, he⟩ := h z
      have hn₀ : n ≠ 0 := fun hz => hn (by rw [hz]; rfl)
      have hd : (q : R) ∣ n := hcop.symm.dvd_of_dvd_mul_left
        (by rw [hcross m n hn₀ he]; exact dvd_mul_left _ _)
      obtain ⟨t, ht⟩ := hd
      intro hz
      apply hn
      rw [ht]
      change (q : R).val (unitaryToUnramified G z) * t.val (unitaryToUnramified G z) = 0
      rw [hz, zero_mul]
    · calc
        b * p = p * b := mul_comm _ _
        _ = a * (q : R) := hcross a b hb rfl
        _ = (q : R) * a := mul_comm _ _)

end UnitaryRegularScalarPresentation
end Langlands.Plancherel
