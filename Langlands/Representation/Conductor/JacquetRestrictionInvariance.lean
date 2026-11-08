import Langlands.Representation.Conductor.SphericalTests
import Langlands.Representation.Conductor.JacquetLevelInvariance
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Group.GL.MirabolicProjection

/-! # From Levi restrictions to Jacquet invariance -/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg Langlands.GeneralLinear.Mirabolic

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F)

private theorem standardCharacter_radical (x : Fin (n + 1) → F) :
    (standardCharacter ψ (n + 1) (radicalToUpperUnipotent (radicalElement x)) : ℂ) =
      ψ.complex (x (Fin.last n)) := by
  rw [standardCharacter_apply, Fin.sum_univ_castSucc]
  congr 1
  have hzero : ∀ i : Fin n,
      (radicalToUpperUnipotent (radicalElement x)).val i.castSucc.castSucc
        i.castSucc.succ = 0 := by
    intro i
    have he : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    rw [he]
    change (radicalElement x).val.val.val _ _ = 0
    rw [radicalElement_first]
    have hi : i.castSucc ≠ i.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    simp only [Fin.castSucc_inj, ite_eq_right hi]
  simp only [hzero, Finset.sum_const_zero, zero_add]
  exact radicalElement_last x (Fin.last n)

/-- A Whittaker value on the mirabolic is determined by its Levi restriction
and the final coordinate of the radical. -/
theorem whittaker_mirabolic_value (W : WhittakerFunctions ψ (n + 1))
    (p : mirabolic (n + 1) F) :
    W.val p.val = ψ.complex (lastColumn p (Fin.last n)) *
      W.val (rankInclusion 1 (projection p)) := by
  have he := congrArg Subtype.val (eq_radicalElement_mul_levi p)
  rw [he]
  exact (W.property (radicalToUpperUnipotent (radicalElement (lastColumn p)))
    (rankInclusion 1 (projection p))).trans
      (congrArg (fun c : ℂ => c * W.val (rankInclusion 1 (projection p)))
        (standardCharacter_radical ψ _))

/-- Equality on the corank-one Levi slice implies equality on the full mirabolic. -/
theorem whittaker_mirabolic_eq_of_levi_eq (W W' : WhittakerFunctions ψ (n + 1))
    (h : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (rankInclusion 1 g) = W'.val (rankInclusion 1 g)) :
    ∀ p : mirabolic (n + 1) F, W.val p.val = W'.val p.val := by
  intro p
  rw [whittaker_mirabolic_value ψ W p, whittaker_mirabolic_value ψ W' p, h]

/-- The support condition needed for the integral radical: each last-row entry
of the smaller matrix is integral whenever its Levi-slice value is nonzero. -/
def HasIntegralLastRowSupport (O : Subring F) (W : WhittakerFunctions ψ (n + 1)) : Prop :=
  ∀ g : Langlands.GeneralLinear (n + 1) F,
    W.val (rankInclusion 1 g) ≠ 0 → ∀ j, g.val (Fin.last n) j ∈ O

omit [TopologicalSpace F] in
private theorem projection_mem_integral (O : Subring F) (h : mirabolic (n + 1) F)
    (hh : h.val ∈ integralSubgroup O (n + 1)) :
    projection h ∈ integralSubgroup O n := by
  obtain ⟨ha, hb⟩ := (mem_integralSubgroup O (n + 1) h.val).1 hh
  exact (mem_integralSubgroup O n (projection h)).2
    ⟨fun i j => ha i.castSucc j.castSucc, fun i j => hb i.castSucc j.castSucc⟩

/-- Integral last-row support removes the radical phase, so right integral
Levi invariance implies right `H(0)` invariance on the whole mirabolic. -/
theorem right_jacquet_on_mirabolic_of_integral_support (O : Subring F)
    (hψ : ∀ x ∈ O, ψ x = 1) (W : WhittakerFunctions ψ (n + 1))
    (hK : ∀ (g : Langlands.GeneralLinear (n + 1) F)
      (k : integralSubgroup O n),
      W.val (rankInclusion 1 (g * k.val)) = W.val (rankInclusion 1 g))
    (hS : HasIntegralLastRowSupport ψ O W) :
    ∀ h ∈ fieldJacquetMirabolic O (n + 1), ∀ p : mirabolic (n + 1) F,
      W.val (p.val * h) = W.val p.val := by
  intro h hh p
  let hP : mirabolic (n + 1) F := ⟨h, hh.2⟩
  have hproj := projection_mem_integral O hP hh.1
  have hval := hK (projection p) ⟨projection hP, hproj⟩
  change W.val ((p * hP).val) = W.val p.val
  rw [whittaker_mirabolic_value ψ W (p * hP), whittaker_mirabolic_value ψ W p,
    map_mul, hval]
  by_cases hz : W.val (rankInclusion 1 (projection p)) = 0
  · simp only [hz, mul_zero]
  · have hrow := hS (projection p) hz
    have hcol : ∀ j, lastColumn hP j ∈ O := by
      intro j
      exact ((mem_integralSubgroup O (n + 1) h).1 hh.1).1 j.castSucc (Fin.last (n + 1))
    have hdot : ((projection p).val.mulVec (lastColumn hP)) (Fin.last n) ∈ O := by
      change (∑ j, (projection p).val (Fin.last n) j * lastColumn hP j) ∈ O
      exact O.sum_mem fun j _ => O.mul_mem (hrow j) (hcol j)
    have hphase : ψ.complex (((projection p).val.mulVec (lastColumn hP)) (Fin.last n)) = 1 := by
      change (ψ (((projection p).val.mulVec (lastColumn hP)) (Fin.last n)) : ℂ) = 1
      rw [hψ _ hdot]
      rfl
    rw [lastColumn_mul, Pi.add_apply, AddChar.map_add_eq_mul, hphase, one_mul]

section Model

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
  (ℓ : glFunctionals ψ (n + 1) π)

/-- Restriction of the actual coefficient model to the actual mirabolic. -/
def modelMirabolicRestriction : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
    (mirabolic (n + 1) F → ℂ) where
  toFun w p := w.val.val p.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Original-carrier restriction injectivity transfers to its actual coefficient image. -/
theorem modelMirabolicRestriction_injective_of_carrier
    (h : Function.Injective (fun v : V => fun p : mirabolic (n + 1) F =>
      ℓ.val (π p.val v))) :
    Function.Injective (modelMirabolicRestriction ψ π ℓ) := by
  intro w w' he
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ w
  obtain ⟨v', rfl⟩ := modelMap_surjective π ℓ w'
  exact congrArg (modelMap π ℓ) (h he)

/-- Supplied restriction injectivity lifts equality on the Levi slice to actual
fixed-vector membership for any subgroup of the full group. -/
theorem mem_fixedVectors_of_levi_restriction
    (hinj : Function.Injective (modelMirabolicRestriction ψ π ℓ))
    (H : Subgroup (Langlands.GeneralLinear ((n + 1) + 1) F))
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : ∀ h ∈ H, ∀ g : Langlands.GeneralLinear (n + 1) F,
      w.val.val (rankInclusion 1 g * h) = w.val.val (rankInclusion 1 g)) :
    w ∈ fixedVectors (modelRepresentation π ℓ) H := by
  intro h
  apply hinj
  apply funext
  exact whittaker_mirabolic_eq_of_levi_eq ψ
    ((modelRepresentation π ℓ h.val w).val) w.val (hw h h.property)

/-- Integral last-row support, integral Levi invariance and supplied mirabolic
restriction injectivity give global `H(0)` fixedness on the unchanged model. -/
theorem mem_jacquetFixedVectors_of_integral_support (O : Subring F)
    (hψ : ∀ x ∈ O, ψ x = 1)
    (hinj : Function.Injective (modelMirabolicRestriction ψ π ℓ))
    (w : (coefficientModel π ℓ).toSubmodule)
    (hK : ∀ (g : Langlands.GeneralLinear (n + 1) F)
      (k : integralSubgroup O n),
      w.val.val (rankInclusion 1 (g * k.val)) = w.val.val (rankInclusion 1 g))
    (hS : HasIntegralLastRowSupport ψ O w.val) :
    w ∈ fixedVectors (modelRepresentation π ℓ) (fieldJacquetMirabolic O (n + 1)) := by
  apply mem_fixedVectors_of_levi_restriction ψ π ℓ hinj _ w
  intro h hh g
  exact right_jacquet_on_mirabolic_of_integral_support ψ O hψ w.val hK hS
    h hh (levi g)

/-- The specialization uses exactly the published restriction-invariance predicate;
integral support and restriction injectivity remain separate inputs. -/
theorem mem_jacquetFixedVectors_of_integral_restriction [ValuativeRel F]
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    (hinj : Function.Injective (modelMirabolicRestriction ψ π ℓ))
    (w : (coefficientModel π ℓ).toSubmodule)
    (hK : IsIntegralInvariantOnRestriction π ℓ w)
    (hS : HasIntegralLastRowSupport ψ (ValuativeRel.valuation F).integer w.val) :
    w ∈ fixedVectors (modelRepresentation π ℓ)
      (fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1)) :=
  mem_jacquetFixedVectors_of_integral_support ψ π ℓ _ hψ hinj w hK hS

end Model

end Langlands.Conductor
