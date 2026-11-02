import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Langlands.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
import Mathlib.NumberTheory.FunctionField

/-! # Extending actual curve places to finite field extensions -/

noncomputable section

universe u v w

namespace Langlands.Global

variable {k : Type u} {K : Type v} {F : Type w}
  [Field k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra K F]
  [IsScalarTower k K F] [FiniteDimensional K F]

private def curvePlaceExtensionData (p : AlgebraicCurve.Place k K) :
    {V : ValuationSubring F // IsDiscreteValuationRing V ∧
      (∀ x : K, x ∈ p.toValuationSubring → algebraMap K F x ∈ V) ∧
      (∀ x : p.toValuationSubring, x ∈ IsLocalRing.maximalIdeal p.toValuationSubring →
        algebraMap K F (x : K) ∈ V.nonunits)} :=
  ⟨Classical.choose
      (p.toValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
        (inferInstance : IsDiscreteValuationRing p.toValuationSubring)),
    Classical.choose_spec
      (p.toValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
        (inferInstance : IsDiscreteValuationRing p.toValuationSubring))⟩

private theorem valuationSubring_ne_top_of_dvr (V : ValuationSubring F)
    [IsDiscreteValuationRing V] : V ≠ ⊤ := by
  intro h
  have hf : IsField V := by
    subst V
    exact (Subring.topEquiv : (⊤ : Subring F) ≃+* F).toMulEquiv.isField
      (Field.toIsField F)
  exact IsDiscreteValuationRing.not_isField V hf

/-- A chosen actual discrete curve place extending `p` to the finite extension `F / K`. -/
def curvePlaceExtension (p : AlgebraicCurve.Place k K) : AlgebraicCurve.Place k F := by
  let d := curvePlaceExtensionData (F := F) p
  letI : IsDiscreteValuationRing d.val := d.property.1
  exact
    { toValuationSubring := d.val
      algebraMap_mem' := fun a => by
        rw [IsScalarTower.algebraMap_apply k K F a]
        exact d.property.2.1 _ (p.algebraMap_mem' a)
      ne_top' := valuationSubring_ne_top_of_dvr d.val
      isPrincipalIdealRing' := inferInstance }

theorem curvePlaceExtension_mem (p : AlgebraicCurve.Place k K) {x : K}
    (hx : x ∈ p.toValuationSubring) :
    algebraMap K F x ∈ (curvePlaceExtension (F := F) p).toValuationSubring :=
  (curvePlaceExtensionData (F := F) p).property.2.1 x hx

theorem curvePlaceExtension_dominates (p : AlgebraicCurve.Place k K)
    (x : p.toValuationSubring) (hx : x ∈ IsLocalRing.maximalIdeal p.toValuationSubring) :
    algebraMap K F (x : K) ∈ (curvePlaceExtension (F := F) p).toValuationSubring.nonunits :=
  (curvePlaceExtensionData (F := F) p).property.2.2 x hx

/-- The chosen extension restricts to exactly the original valuation subring. -/
@[simp]
theorem curvePlaceExtension_mem_iff (p : AlgebraicCurve.Place k K) (x : K) :
    algebraMap K F x ∈ (curvePlaceExtension (F := F) p).toValuationSubring ↔
      x ∈ p.toValuationSubring := by
  refine ⟨fun hx => ?_, curvePlaceExtension_mem p⟩
  by_contra h
  have hx0 : x ≠ 0 := fun he => h (he ▸ p.toValuationSubring.zero_mem)
  have hi : x⁻¹ ∈ p.toValuationSubring.nonunits :=
    p.toValuationSubring.inv_mem_nonunits_iff.mpr (Or.inr h)
  have hm := curvePlaceExtension_dominates (F := F) p
    ⟨x⁻¹, p.toValuationSubring.nonunits_subset hi⟩
    (ValuationSubring.coe_mem_nonunits_iff.mp hi)
  rw [map_inv₀, ValuationSubring.inv_mem_nonunits_iff] at hm
  exact hm.elim
    (fun he => hx0 ((algebraMap K F).injective (he.trans (map_zero _).symm)))
    (fun hn => hn hx)

@[simp]
theorem curvePlaceExtension_comap (p : AlgebraicCurve.Place k K) :
    (curvePlaceExtension (F := F) p).toValuationSubring.comap (algebraMap K F) =
      p.toValuationSubring := by
  ext x
  exact curvePlaceExtension_mem_iff p x

section FunctionField

variable (k F) [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F]

/-- One actual place of the function field, chosen above the rational point zero. -/
def curvePlaceReference : AlgebraicCurve.Place k F :=
  curvePlaceExtension (F := F)
    (AlgebraicCurve.RationalFunctionField.placeOfPoint k 0)

theorem curvePlace_nonempty : Nonempty (AlgebraicCurve.Place k F) :=
  ⟨curvePlaceReference k F⟩

end FunctionField

end Langlands.Global
