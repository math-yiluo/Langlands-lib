import Langlands.GroupScheme.Torus.WeilRestrictionRationalCharacters
import Langlands.Geometry.Building.KPCharacterCongruence

/-! # Congruence for all geometric characters of Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

variable (k E Ω : Type u) [Field k] [Field E] [Field Ω]
  [Algebra k E] [Algebra k Ω] [FiniteDimensional k E]
  (h : Function.Bijective (embeddingEvaluation k E Ω))
  (ω : AddValuation E (WithTop ℝ)) (ν : AddValuation Ω (WithTop ℝ))
  (hν : ∀ τ : E →ₐ[k] Ω, ∀ x : E, ν (τ x) = ω x)

include h hν

/-- Valuation-preserving embeddings carry unit congruence into all geometric character tests. -/
theorem weilGm_rationalExtend_mem_characterCongruence
    (r : ℝ≥0) (x : rationalPoints (WeilGm.groupScheme (CommRingCat.of k) E))
    (hx : WeilGm.rationalUnitsEquiv k E x ∈ addValuationUnitFiltration ω r) :
    rationalExtend k Ω (WeilGm.groupScheme (CommRingCat.of k) E) x ∈
      characterCongruence ν
        (baseChanged k Ω (WeilGm.groupScheme (CommRingCat.of k) E)) r := by
  classical
  rw [mem_characterCongruence]
  intro χ
  rw [WeilGm.rationalCharacterEval_extend_eq_prod k E Ω h]
  apply Subgroup.prod_mem
  intro τ _
  apply Subgroup.zpow_mem
  exact map_addValuationUnitFiltration_le ω ν τ.toRingHom (hν τ) r
    (Subgroup.mem_map.mpr ⟨_, hx, rfl⟩)

/-- At positive depth it suffices to bound the difference of the original unit from one. -/
theorem weilGm_rationalExtend_mem_characterCongruence_of_pos
    {r : ℝ≥0} (hr : 0 < r)
    (x : rationalPoints (WeilGm.groupScheme (CommRingCat.of k) E))
    (hx : ((r : ℝ) : WithTop ℝ) ≤ ω ((WeilGm.rationalUnitsEquiv k E x : E) - 1)) :
    rationalExtend k Ω (WeilGm.groupScheme (CommRingCat.of k) E) x ∈
      characterCongruence ν
        (baseChanged k Ω (WeilGm.groupScheme (CommRingCat.of k) E)) r := by
  exact weilGm_rationalExtend_mem_characterCongruence k E Ω h ω ν hν r x
    ((mem_addValuationUnitFiltration_of_pos ω hr _).mpr hx)

/-- The unit-coordinate form directly supplies every character difference bound. -/
theorem weilGm_rationalCharacterEval_sub_one_le_of_pos
    {r : ℝ≥0} (hr : 0 < r) (t : Eˣ)
    (ht : ((r : ℝ) : WithTop ℝ) ≤ ω ((t : E) - 1))
    (χ : rationalCharacters
      (baseChanged k Ω (WeilGm.groupScheme (CommRingCat.of k) E))) :
    ((r : ℝ) : WithTop ℝ) ≤ ν
      ((rationalCharacterEval χ
        (rationalExtend k Ω (WeilGm.groupScheme (CommRingCat.of k) E)
          ((WeilGm.rationalUnitsEquiv k E).symm t)) : Ω) - 1) := by
  have hx := weilGm_rationalExtend_mem_characterCongruence_of_pos
    k E Ω h ω ν hν hr ((WeilGm.rationalUnitsEquiv k E).symm t)
    (by simpa only [MulEquiv.apply_symm_apply] using ht)
  exact ((mem_characterCongruence ν _ r _).mp hx χ).2

/-- Unit-coordinate extension restricts to a homomorphism of congruence subgroups. -/
def weilGm_unitCongruenceHom (r : ℝ≥0) :
    addValuationUnitFiltration ω r →*
      characterCongruence ν
        (baseChanged k Ω (WeilGm.groupScheme (CommRingCat.of k) E)) r where
  toFun t := ⟨WeilGm.extendedUnitPoint k E Ω t.val, by
    exact weilGm_rationalExtend_mem_characterCongruence k E Ω h ω ν hν r
      ((WeilGm.rationalUnitsEquiv k E).symm t.val)
      (by simpa only [MulEquiv.apply_symm_apply] using t.property)⟩
  map_one' := Subtype.ext (map_one (WeilGm.extendedUnitPoint k E Ω))
  map_mul' x y := Subtype.ext (map_mul (WeilGm.extendedUnitPoint k E Ω) x.val y.val)

@[simp] theorem weilGm_unitCongruenceHom_coe (r : ℝ≥0)
    (t : addValuationUnitFiltration ω r) :
    (weilGm_unitCongruenceHom k E Ω h ω ν hν r t :
      rationalPoints (baseChanged k Ω (WeilGm.groupScheme (CommRingCat.of k) E))) =
        WeilGm.extendedUnitPoint k E Ω t.val := rfl

end Langlands.Geometry.Building
