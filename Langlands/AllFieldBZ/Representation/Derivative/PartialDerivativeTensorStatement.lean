import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.AllFieldBZ.Representation.Derivative.Partial
import Langlands.Representation.Derivative.PartialDerivativeTensorStatement

/-!
# All-field port of `Langlands.Representation.Derivative.PartialDerivativeTensorStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.PartialDerivativeTensorStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero partialDerivative partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero topDerivative topDerivative_eq topDerivative_zero
universe uF uG uV₁ uV₂ uV₃ uW₁ uW₂ uW₃ uV

namespace PartialTensor
open Langlands.Derivative.PartialTensor
variable {G H : Type uG} [Group G] [Group H]
variable {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
variable {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
variable {V₃ : Type uV₃} [AddCommGroup V₃] [Module ℂ V₃]
variable {W₁ : Type uW₁} [AddCommGroup W₁] [Module ℂ W₁]
variable {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
variable {W₃ : Type uW₃} [AddCommGroup W₃] [Module ℂ W₃]

/-! ## The raw exterior tensor product of `G × H` -/

/-! ## `G` acting on `V ⊗[ℂ] W` through the first factor -/

/-! ## Smoothness -/

section Topology
variable [TopologicalSpace G] [TopologicalSpace H]

/-! ## The two bifunctors -/

end Topology
end PartialTensor
/-! ## The functors for `GL_k × GL_m` -/

variable {F : LocalFieldPackage.{uF}}

/-- The top derivative `GL_m → GL_0`: the published order-`m` derivative followed by the
rank transport along `m - m = 0`. -/
def topDerivative (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) := by
  letI := T.topology
  exact generalLinearDerivative T ψ m m (Nat.le_refl m) ⋙ generalLinearRankCast T (Nat.sub_self m)

/-! ## Unfolding lemmas -/

theorem topDerivative_eq (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    letI := T.topology
    topDerivative.{uF, uV} T ψ m =
      generalLinearDerivative T ψ m m (Nat.le_refl m) ⋙
        generalLinearRankCast T (Nat.sub_self m) :=
  rfl

/-- The zeroth top derivative is the identity functor of `GL_0`. -/
theorem topDerivative_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    topDerivative.{uF, uV} T ψ 0 = 𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :=
  rfl

/-! ## The comparison -/

end Langlands.AllFieldBZ.Derivative
