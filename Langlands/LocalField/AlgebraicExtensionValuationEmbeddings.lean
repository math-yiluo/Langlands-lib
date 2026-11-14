import Langlands.LocalField.AlgebraicExtensionValuation
import Langlands.LocalField.AddValuationUnitFiltration

/-! # Algebra embeddings preserve normalized extension valuations -/

noncomputable section

universe u v w

open scoped NNReal

namespace Langlands.LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : Type v) (L : Type w) [Field E] [Field L]
  [Algebra F E] [Algebra F L] [Algebra.IsAlgebraic F E] [Algebra.IsAlgebraic F L]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F

/-- A base-field algebra embedding preserves the spectral multiplicative valuation. -/
theorem spectralValuation_algHom (f : E →ₐ[F] L) (x : E) :
    LocalGalois.spectralValuation F L (f x) =
      LocalGalois.spectralValuation F E x := by
  apply NNReal.eq
  change spectralNorm F L (f x) = spectralNorm F E x
  simp only [spectralNorm, minpoly.algHom_eq f f.injective]

/-- Algebra embeddings preserve the extension valuation normalized over the same local field. -/
theorem algebraicExtensionAddValuation_algHom (f : E →ₐ[F] L) (x : E) :
    algebraicExtensionAddValuation F L (f x) =
      algebraicExtensionAddValuation F E x := by
  simp only [algebraicExtensionAddValuation, logAdditiveValuation_apply,
    spectralValuation_algHom F E L f x]

/-- The unit map of an algebra embedding restricts to every normalized congruence subgroup. -/
def algebraicExtensionUnitCongruenceHom (f : E →ₐ[F] L) (r : ℝ≥0) :
    addValuationUnitFiltration (algebraicExtensionAddValuation F E) r →*
      addValuationUnitFiltration (algebraicExtensionAddValuation F L) r where
  toFun x := ⟨Units.map f.toMonoidHom x.val,
    map_addValuationUnitFiltration_le
      (algebraicExtensionAddValuation F E) (algebraicExtensionAddValuation F L)
      f.toRingHom (algebraicExtensionAddValuation_algHom F E L f) r
      (Subgroup.mem_map.mpr ⟨x.val, x.property, rfl⟩)⟩
  map_one' := Subtype.ext (map_one (Units.map f.toMonoidHom))
  map_mul' x y := Subtype.ext (map_mul (Units.map f.toMonoidHom) x.val y.val)

@[simp] theorem algebraicExtensionUnitCongruenceHom_coe
    (f : E →ₐ[F] L) (r : ℝ≥0)
    (x : addValuationUnitFiltration (algebraicExtensionAddValuation F E) r) :
    (algebraicExtensionUnitCongruenceHom F E L f r x : Lˣ) =
      Units.map f.toMonoidHom x.val := rfl

end Langlands.LocalField
