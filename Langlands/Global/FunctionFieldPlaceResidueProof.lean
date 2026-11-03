import Langlands.Global.FunctionFieldPlaceResidueStatement

/-! # Residue finiteness from one-dimensional overring arithmetic -/

noncomputable section

universe u

open IntermediateField Polynomial AlgebraicCurve
open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel

namespace Langlands.Global

section Parameter

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (s : F) [FiniteDimensional k⟮s⟯ F]
  (v : Place k F)

private theorem finite_residue_of_parameter_mem
    (hs : s ∈ v.toValuationSubring) : Module.Finite k v.ResidueField := by
  let R := Algebra.adjoin k ({s} : Set F)
  have hR (a : R) : algebraMap R F a ∈ v.toValuationSubring :=
    CurveModel.adjoin_le_valuationSubring v.toValuationSubring v.algebraMap_mem'
      (Set.singleton_subset_iff.mpr hs) a.property
  let B : Subalgebra R F :=
    { v.toValuationSubring.toSubring with algebraMap_mem' := hR }
  let : Algebra k B := inferInstanceAs (Algebra k v.toValuationSubring)
  let : IsScalarTower k R B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsLocalRing B := inferInstanceAs (IsLocalRing v.toValuationSubring)
  have hmax : IsLocalRing.maximalIdeal B ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field v.toValuationSubring
  have hfl : IsFiniteLength R (IsLocalRing.ResidueField B) :=
    (Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
      (K := k⟮s⟯) B).2.2 (IsLocalRing.maximalIdeal B) hmax
  let : IsNoetherian R (IsLocalRing.ResidueField B) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  let : Module.Finite R (IsLocalRing.ResidueField B) := inferInstance
  let : Algebra.FiniteType k (IsLocalRing.ResidueField B) :=
    Algebra.FiniteType.trans
      (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton s))
      (inferInstance : Algebra.FiniteType R (IsLocalRing.ResidueField B))
  exact finite_of_finite_type_of_isJacobsonRing k (IsLocalRing.ResidueField B)

end Parameter

theorem functionFieldPlaceResidue : FunctionFieldPlaceResidueStatement.{u} := by
  intro k F _ _ _ _ _ _ v
  let s : F := algebraMap (RatFunc k) F (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ F := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  rcases v.toValuationSubring.mem_or_inv_mem s with hs | hs
  · exact finite_residue_of_parameter_mem k F s v hs
  · have hinv : k⟮s⁻¹⟯ = k⟮s⟯ :=
      le_antisymm
        (adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self k s)))
        (adjoin_simple_le_iff.mpr (by
          simpa using inv_mem (mem_adjoin_simple_self k s⁻¹)))
    let : FiniteDimensional k⟮s⁻¹⟯ F := by rw [hinv]; infer_instance
    exact finite_residue_of_parameter_mem k F s⁻¹ v hs

end Langlands.Global
