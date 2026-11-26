import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Classification.Supercuspidal

/-! # Jacquet modules of representations containing a non-maximal level-zero simple type -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uρ uπ

/-- **BK93 (7.3.2), first remark, and (7.3.6)(i), kind (b).** A smooth representation
containing a level-zero simple type of period `e ≥ 2` has a nonzero Jacquet module for some
conjugate of the unipotent radical of a proper standard block parabolic. -/
def LevelZeroNonmaximalTypeJacquetStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (J : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ J)
      (L : LatticeChain 𝒪[F] F (Fin n → F)) (e : ℕ),
      IsLevelZeroSimpleTypeData (W := (ρ : Type uρ)) L e (glRepresentationToAut ρ) → 2 ≤ e →
      ∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F), ContainsType π ρ →
        ∃ (B : GeneralLinear.BlockShape n) (g : GeneralLinear n F), B.parabolic F ≠ ⊤ ∧
          ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g))

end Langlands.BushnellKutzko
