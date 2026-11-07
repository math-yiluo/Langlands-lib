import Langlands.Global.AdelicTensorBaseChange

/-! # Bijectivity of the canonical full adelic tensor maps -/

noncomputable section

universe u

namespace Langlands.Global

/-- The full tensor map for number fields is bijective, including all infinite factors. -/
def NumberFieldAdeleTensorMapBijectiveStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L],
    Function.Bijective (numberFieldAdeleTensorMap K L)

/-- The full curve-place tensor map is bijective for arbitrary finite global extensions. -/
def CurvePlaceAdeleTensorMapBijectiveStatement : Prop :=
  ∀ (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L],
    letI : Algebra (RatFunc k) L :=
      ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
    letI : IsScalarTower (RatFunc k) K L :=
      .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower k (RatFunc k) L :=
      .of_algebraMap_eq fun a => by
        change algebraMap k L a =
          algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
        rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
          ← IsScalarTower.algebraMap_apply k K L]
    letI : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
    Function.Bijective (curvePlaceAdeleTensorMap k K L)

/-- The canonical full adelic tensor maps are bijective in both characteristics. -/
def AdelicTensorBaseChangeStatement : Prop :=
  CurvePlaceAdeleTensorMapBijectiveStatement.{u} ∧
    NumberFieldAdeleTensorMapBijectiveStatement.{u}

end Langlands.Global
