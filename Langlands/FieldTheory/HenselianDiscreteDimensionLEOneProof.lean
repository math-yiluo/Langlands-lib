import Langlands.FieldTheory.HenselianDiscreteDimensionLEOneStatement
import Langlands.FieldTheory.IntegerValuationRealization
import Langlands.FieldTheory.HenselianRealGaloisProlongationProof
import Langlands.ClassFieldTheory.Local.SeparableInertiaFullNorm
import Mathlib.FieldTheory.IsSepClosed

/-! # Norm surjectivity over Henselian discrete fields with algebraically closed residue -/

noncomputable section

universe u

open scoped NNReal WithZero

namespace Langlands.FieldTheory

open Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

/-- Henselian discretely valued fields with algebraically closed residue
satisfy the exact finite-separable determinant unit-norm criterion. -/
theorem henselianDiscreteDimensionLEOne :
    HenselianDiscreteDimensionLEOneStatement.{u} := by
  intro K _ v hv hH hres
  let : HenselianLocalRing v.valuationSubring := hH
  let : IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring) := hres
  let ν := integerValuationToReal v
  have hν : HenselianLocalRing ν.valuationSubring := by
    dsimp only [ν]
    rw [integerValuationToReal_valuationSubring]
    exact hH
  let Ω := SeparableClosure K
  obtain ⟨w, hw, hinv⟩ := henselianRealGaloisProlongation K ν hν Ω
  have hA : AmbientHyp (U := K) w := by
    refine ⟨hinv, ?_, ?_, ?_⟩
    · let : HenselianLocalRing w.valuationSubring :=
        Langlands.LocalGalois.Separable.sepClosed_henselian _
      exact valHensel_of_henselian w
    · rw [hw]
      exact integerValuationToReal_valResidueRoot v
    · rw [hw]
      exact integerValuationToReal_exists_uniformizer v hv
  intro E _ _ _ _ L _ _ _ _
  let : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K E L
  let f : L →ₐ[K] Ω := IsSepClosed.lift
  let : Algebra L Ω := f.toRingHom.toAlgebra
  let : Algebra E Ω := (f.toRingHom.comp (algebraMap E L)).toAlgebra
  let : IsScalarTower E L Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (f.commutes x).symm)
  let : IsScalarTower K E Ω := IsScalarTower.to₁₂₄ K E L Ω
  exact hA.surjective_unit_norm (E := E) (M := L)

end Langlands.FieldTheory
