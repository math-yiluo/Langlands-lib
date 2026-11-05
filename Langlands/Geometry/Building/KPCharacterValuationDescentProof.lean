import Langlands.Geometry.Building.KPCharacterValuationDescentStatement
import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisDescent
import Langlands.GroupScheme.Rational.TorusCharacterSpectral

/-! # Descent of the character-valuation kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.Plancherel.TorusNormKernel

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

section Valuation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F

/-- A canonical valuation unit is a unit for the compatible local-field norm. -/
private theorem localNorm_eq_one_of_valuation_eq_one {x : F}
    (hx : ValuativeRel.valuation F x = 1) : ‖x‖ = 1 := by
  have hle := (LocalGalois.localNormedField_le F x 1).mpr (by simp [hx])
  have hge := (LocalGalois.localNormedField_le F 1 x).mpr (by simp [hx])
  simpa only [norm_one] using le_antisymm hle hge

/-- A unit-valued field norm forces unit valuation in the unramified closure. -/
private theorem fixedFieldValuation_map_eq_one_of_norm
    (L : FiniteGaloisIntermediateField F (UnramifiedClosure F)) {x : L}
    (hx : ValuativeRel.valuation F (Algebra.norm F x) = 1) :
    LocalGalois.Separable.fixedFieldValuation F
      (algebraMap L (UnramifiedClosure F) x) = 1 := by
  classical
  rw [LocalGalois.Separable.fixedFieldValuation_eq_spectralValuation]
  apply NNReal.eq
  change spectralNorm F (UnramifiedClosure F) (algebraMap L (UnramifiedClosure F) x) = 1
  rw [← spectralNorm.eq_of_tower]
  apply (pow_eq_one_iff_of_nonneg (spectralNorm_nonneg x)
    (Fintype.card_ne_zero (α := L ≃ₐ[F] L))).mp
  rw [LocalGalois.spectralNorm_pow_card_galois]
  exact localNorm_eq_one_of_valuation_eq_one F hx

end Valuation

set_option maxHeartbeats 800000 in
/-- The exact public character-valuation kernel descent proposition. -/
theorem characterValuationKernelDescent_proof :
    CharacterValuationKernelDescentStatement.{u} := by
  intro F _ _ _ _ G _
  rw [← characterValuationKernel_eq_rationalCommonNormKernel]
  apply le_antisymm
  · exact comap_characterValuationKernel_le (ValuativeRel.valuation F)
      (LocalGalois.Separable.fixedFieldValuation F) G
  · intro g hg
    change GaloisPointComparison.rationalExtend F (UnramifiedClosure F) G g ∈
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
        (GaloisPointComparison.baseChanged F (UnramifiedClosure F) G)
    rw [mem_characterValuationKernel] at hg ⊢
    intro ψ
    obtain ⟨L, ψL, hψL⟩ :=
      AffineCharacterFiniteGalois.exists_finiteGalois_character G ψ
    rw [← hψL g]
    apply fixedFieldValuation_map_eq_one_of_norm F L
    rw [← normCharacter_eval ψL g]
    exact hg (normCharacter ψL)

end Langlands.Geometry.Building
