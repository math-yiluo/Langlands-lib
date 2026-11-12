import Langlands.Algebra.UnitizationTensorComparisonStatements

/-!
# Renard I.2.1: proofs of the unitized tensor comparison and the unitization uniqueness
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationTensorComparison

open MulOpposite CompatibleUnitizationTensor

universe uK uA uX uY

section Kernel

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
  [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
  [IsScalarTower k A Y] [SMulCommClass k A Y]

/-- The class in `Q = TA ⧸ H` of the original pure tensor, as a biadditive map. -/
def quotientBiadditive : X →+ Y →+ ScalarQuotient k A X Y :=
  (NonUnitalModuleTensor.biadditive A X Y).compr₂ (scalarRelations k A X Y).mkQ.toAddMonoidHom

omit [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] [IsScalarTower k Aᵐᵒᵖ X]
  [SMulCommClass k Aᵐᵒᵖ X] [IsScalarTower k A Y] [SMulCommClass k A Y] in
theorem quotientBiadditive_apply (x : X) (y : Y) :
    quotientBiadditive k A X Y x y =
      Submodule.Quotient.mk (p := scalarRelations k A X Y) (NonUnitalModuleTensor.tmul A X Y x y) :=
  rfl

omit [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] [IsScalarTower k Aᵐᵒᵖ X]
  [SMulCommClass k Aᵐᵒᵖ X] [IsScalarTower k A Y] [SMulCommClass k A Y] in
theorem quotientBiadditive_isBalanced :
    NonUnitalModuleTensor.IsBalanced A (quotientBiadditive k A X Y) := fun a x y => by
  rw [quotientBiadditive_apply, quotientBiadditive_apply, NonUnitalModuleTensor.tmul_balanced]

omit [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] [IsScalarTower k Aᵐᵒᵖ X]
  [SMulCommClass k Aᵐᵒᵖ X] [IsScalarTower k A Y] [SMulCommClass k A Y] in
theorem quotientBiadditive_isScalarBalanced :
    IsScalarBalanced k (quotientBiadditive k A X Y) := fun c x y => by
  rw [quotientBiadditive_apply, quotientBiadditive_apply]
  exact (Submodule.Quotient.eq _).mpr (scalarDifference_mem k A X Y c x y)

/-- The inverse `TU →+ Q` of the descended comparison. -/
def inverse : UnitizedTensor k A X Y →+ ScalarQuotient k A X Y :=
  unitizedLift k A (quotientBiadditive k A X Y) (quotientBiadditive_isBalanced k A X Y)
    (quotientBiadditive_isScalarBalanced k A X Y)

theorem inverse_comp_comparison :
    (inverse k A X Y).comp (comparison k A X Y) = (scalarRelations k A X Y).mkQ.toAddMonoidHom :=
  NonUnitalModuleTensor.hom_ext A fun _ _ => rfl

theorem descendedComparison_inverse (t : UnitizedTensor k A X Y) :
    descendedComparison k A X Y (inverse k A X Y t) = t := by
  have h : (descendedComparison k A X Y).comp (inverse k A X Y) = AddMonoidHom.id _ :=
    unitizedHom_ext k A fun _ _ => rfl
  exact DFunLike.congr_fun h t

theorem inverse_descendedComparison (s : ScalarQuotient k A X Y) :
    inverse k A X Y (descendedComparison k A X Y s) = s := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  exact DFunLike.congr_fun (inverse_comp_comparison k A X Y) t

end Kernel

theorem scalarQuotientComparison : ScalarQuotientComparisonStatement.{uK, uA, uX, uY} := by
  intro k A X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨le_antisymm ?_ (scalarRelations_le_ker k A X Y), ?_⟩
  · intro t ht
    rw [LinearMap.mem_ker] at ht
    have h0 : descendedComparison k A X Y (Submodule.Quotient.mk t) = 0 := ht
    have h1 := inverse_descendedComparison k A X Y (Submodule.Quotient.mk t)
    rw [h0, map_zero] at h1
    exact (Submodule.Quotient.mk_eq_zero _).mp h1.symm
  · exact Function.bijective_iff_has_inverse.mpr ⟨inverse k A X Y,
      inverse_descendedComparison k A X Y, descendedComparison_inverse k A X Y⟩

theorem nondegenerateUnitizedTensor : NondegenerateUnitizedTensorStatement.{uK, uA, uX, uY} := by
  intro k A X Y _ _ _ _ _ _ _ _ _ hA hX hY
  let _ := NondegenerateTensorScalars.rightModule k hA hX
  let _ := NondegenerateTensorScalars.leftModule k hA hY
  have := NondegenerateScalars.isScalarTower k hA.op hX
  have := NondegenerateScalars.smulCommClass k hA.op hX
  have := NondegenerateScalars.isScalarTower k hA hY
  have := NondegenerateScalars.smulCommClass k hA hY
  refine ⟨fun s t hst => ?_, comparison_surjective k A X Y⟩
  have hH : scalarRelations k A X Y = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨⟨c, x, y⟩, rfl⟩
    exact sub_eq_zero.mpr (NondegenerateTensorScalars.tmul_smul_left_eq k A X Y hA hX hY c x y)
  have hmem : s - t ∈ LinearMap.ker (comparison k A X Y).toIntLinearMap := by
    rw [LinearMap.mem_ker]
    change comparison k A X Y (s - t) = 0
    rw [map_sub, hst, sub_self]
  rw [(scalarQuotientComparison k A X Y).1, hH, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

theorem unitalUnitizedTensor : UnitalUnitizedTensorStatement.{uK, uA, uX, uY} :=
  fun k R X Y _ _ _ _ _ _ _ hX hY =>
    nondegenerateUnitizedTensor k R X Y (IsIdempotented.of_ring R)
      (isNondegenerate_iff_isUnitalModule.mpr hX) (isNondegenerate_iff_isUnitalModule.mpr hY)

theorem unitizationAlgebraUnique : UnitizationAlgebraUniqueStatement.{uK, uA} := by
  intro k A _ _ _ _ _
  refine ⟨⟨fun u v w => mul_assoc u v w, fun u => ⟨one_mul u, mul_one u⟩,
    fun a b => (Unitization.inr_mul k a b).symm⟩, ?_⟩
  intro μ h1l h1r hAA
  have hinl : ∀ r : k, (Unitization.inl r : Unitization k A) = r • (1 : Unitization k A) := by
    intro r
    ext <;> simp
  refine LinearMap.ext₂ fun u v => ?_
  rw [← Unitization.inl_fst_add_inr_snd_eq u, ← Unitization.inl_fst_add_inr_snd_eq v]
  simp only [hinl, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1l, h1r, hAA,
    LinearMap.mul_apply', one_mul, mul_one, Unitization.inr_mul]

/-- All four I.2.1 assertions. -/
theorem statements : Statements.{uK, uA, uX, uY} :=
  ⟨scalarQuotientComparison, nondegenerateUnitizedTensor, unitalUnitizedTensor,
    unitizationAlgebraUnique⟩

end Langlands.Algebra.UnitizationTensorComparison
