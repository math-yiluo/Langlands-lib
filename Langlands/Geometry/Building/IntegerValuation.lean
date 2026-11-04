import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-! # Integer-valued valuation adapters on actual rational characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuation

variable {k : Type u} [Field k]

/-- Source-positive order: restrict the actual valuation to units, identify
`(WithZero (Multiplicative ℤ))ˣ` with `Multiplicative ℤ`, then invert. -/
def orderUnits (v : Valuation k (WithZero (Multiplicative ℤ))) :
    kˣ →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map v.toMonoidHom))⁻¹

theorem orderUnits_toAdd (v : Valuation k (WithZero (Multiplicative ℤ))) (a : kˣ) :
    (orderUnits v a).toAdd = -WithZero.log (v (a : k)) := by
  change -(WithZero.unitsWithZeroEquiv (Units.map v.toMonoidHom a)).toAdd = _
  exact congrArg Neg.neg (WithZero.logEquiv_apply _)

theorem orderUnits_eq_one_iff (v : Valuation k (WithZero (Multiplicative ℤ))) (a : kˣ) :
    orderUnits v a = 1 ↔ v (a : k) = 1 := by
  change (WithZero.unitsWithZeroEquiv (Units.map v.toMonoidHom a))⁻¹ = 1 ↔ _
  rw [inv_eq_one, ← map_one WithZero.unitsWithZeroEquiv,
    WithZero.unitsWithZeroEquiv.injective.eq_iff]
  exact Units.ext_iff

/-- The real order used by the existing `KPApartmentData`. -/
def order (v : Valuation k (WithZero (Multiplicative ℤ))) (a : kˣ) : ℝ :=
  ((orderUnits v a).toAdd : ℝ)

/-- The source-positive integer dual of the actual rational-character evaluations. -/
def rationalCharacterValuation (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    rationalPoints G →* Multiplicative (rationalCharacters G →+ ℤ) :=
  Plancherel.characterValuation (rationalCharacterEvalHom (G := G)) (orderUnits v)

@[simp] theorem rationalCharacterValuation_apply
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (g : rationalPoints G) (χ : rationalCharacters G) :
    (rationalCharacterValuation v G g).toAdd χ =
      (orderUnits v (rationalCharacterEval χ g)).toAdd := rfl

/-- Corrected KP (2.6.3): the character coordinate is the positive field order. -/
theorem rationalCharacterValuation_eval
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (g : rationalPoints G) (χ : rationalCharacters G) :
    (rationalCharacterValuation v G g).toAdd χ =
      -WithZero.log (v (rationalCharacterEval χ g : k)) :=
  orderUnits_toAdd v _

/-- The same actual character valuation in the real dual. -/
def realCharacterValuation (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    rationalPoints G →* Multiplicative (rationalCharacters G →+ ℝ) where
  toFun g := Multiplicative.ofAdd
    ((Int.castAddHom ℝ).comp (rationalCharacterValuation v G g).toAdd)
  map_one' := by
    apply AddMonoidHom.ext
    intro χ
    simp
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro χ
    change ((rationalCharacterValuation v G (g * h)).toAdd χ : ℝ) =
      ((rationalCharacterValuation v G g).toAdd χ : ℝ) +
        ((rationalCharacterValuation v G h).toAdd χ : ℝ)
    rw [map_mul]
    exact Int.cast_add _ _

@[simp] theorem realCharacterValuation_apply
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (g : rationalPoints G) (χ : rationalCharacters G) :
    (realCharacterValuation v G g).toAdd χ = order v (rationalCharacterEval χ g) := rfl

variable {G H : GroupScheme (Spec (CommRingCat.of k))}

theorem rationalCharacterValuation_characterRestrict
    (v : Valuation k (WithZero (Multiplicative ℤ))) (f : H ⟶ G)
    (χ : rationalCharacters G) (y : rationalPoints H) :
    (rationalCharacterValuation v H y).toAdd (characterRestrict f χ) =
      (rationalCharacterValuation v G (rationalPoints.map f y)).toAdd χ := by
  simp only [rationalCharacterValuation_apply, rationalCharacterEval_characterRestrict]

theorem realCharacterValuation_characterRestrict
    (v : Valuation k (WithZero (Multiplicative ℤ))) (f : H ⟶ G)
    (χ : rationalCharacters G) (y : rationalPoints H) :
    (realCharacterValuation v H y).toAdd (characterRestrict f χ) =
      (realCharacterValuation v G (rationalPoints.map f y)).toAdd χ := by
  simp only [realCharacterValuation_apply, rationalCharacterEval_characterRestrict]

theorem rationalCharacterValuation_ker
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (rationalCharacterValuation v G).ker = characterValuationKernel v G := by
  ext g
  rw [rationalCharacterValuation, Plancherel.mem_characterValuation_ker,
    mem_characterValuationKernel]
  exact forall_congr' fun χ => orderUnits_eq_one_iff v _

theorem realCharacterValuation_ker
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (realCharacterValuation v G).ker = characterValuationKernel v G := by
  rw [← rationalCharacterValuation_ker v G]
  ext g
  change ((Int.castAddHom ℝ).comp (rationalCharacterValuation v G g).toAdd = 0) ↔
    (rationalCharacterValuation v G g).toAdd = 0
  constructor
  · intro h
    ext χ
    have hc := DFunLike.congr_fun h χ
    change ((rationalCharacterValuation v G g).toAdd χ : ℝ) = 0 at hc
    exact_mod_cast hc
  · intro h
    simp [h]

/-- Functoriality of the common character kernel uses actual character restriction. -/
theorem map_mem_characterValuationKernel
    (v : Valuation k (WithZero (Multiplicative ℤ))) (f : H ⟶ G)
    {y : rationalPoints H} (hy : y ∈ characterValuationKernel v H) :
    rationalPoints.map f y ∈ characterValuationKernel v G := by
  rw [mem_characterValuationKernel] at hy ⊢
  intro χ
  rw [← rationalCharacterEval_characterRestrict]
  exact hy _

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem orderUnits_normalized :
    orderUnits (FML.normalizedMultiplicativeValuation F) = Plancherel.fieldOrderUnits F := by
  ext a
  change (orderUnits (FML.normalizedMultiplicativeValuation F) a).toAdd =
    (Plancherel.fieldOrderUnits F a).toAdd
  rw [orderUnits_toAdd, Plancherel.fieldOrderUnits_toAdd]

theorem rationalCharacterValuation_normalized
    (G : GroupScheme (Spec (CommRingCat.of F))) :
    rationalCharacterValuation (FML.normalizedMultiplicativeValuation F) G =
      Plancherel.rationalCharacterValuation G := by
  unfold rationalCharacterValuation Plancherel.rationalCharacterValuation
  rw [orderUnits_normalized]

theorem realCharacterValuation_normalized
    (G : GroupScheme (Spec (CommRingCat.of F))) :
    realCharacterValuation (FML.normalizedMultiplicativeValuation F) G =
      Plancherel.rationalNormLogarithm G := by
  apply MonoidHom.ext
  intro g
  apply AddMonoidHom.ext
  intro χ
  change ((rationalCharacterValuation (FML.normalizedMultiplicativeValuation F) G g).toAdd χ : ℝ) =
    (Plancherel.rationalNormLogarithm G g).toAdd χ
  rw [rationalCharacterValuation_normalized,
    Plancherel.rationalNormLogarithm_eq_intValuation]

theorem characterValuationKernel_normalized
    (G : GroupScheme (Spec (CommRingCat.of F))) :
    characterValuationKernel (FML.normalizedMultiplicativeValuation F) G =
      Plancherel.rationalCommonNormKernel G := by
  rw [← rationalCharacterValuation_ker, rationalCharacterValuation_normalized,
    Plancherel.rationalCharacterValuation_ker]

end LocalField

end Langlands.Geometry.Building.IntegerValuation
