import Langlands.Geometry.Building.Kottwitz.NormalizedValuation

/-! # Existence and uniqueness of the normalized splitting-field valuation -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- The spectral valuation on every finite extension of `K` has a unique surjective integer
normalization. No local-field instance on `K` or `L` is assumed. -/
def NormalizedIntermediateValuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L],
    ∃! v : Valuation L (WithZero (Multiplicative ℤ)),
      IsNormalizedIntermediateValuation F L v

end Langlands.Geometry.Building.Kottwitz
