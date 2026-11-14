import Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.Geometric.StandardIntersectionsProof
import Langlands.AllField.Representation.Parabolic.RefinementCharacter
/-! Actual coefficient quotients for a parabolic orbit. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

private def coefficientSubgroupCongr (ρ : Representation ℂ (B.Levi F) V)
    {U U' : Subgroup (B.Levi F)} (h : U = U') :
    Jacquet.Coinvariants ρ U ≃ₗ[ℂ] Jacquet.Coinvariants ρ U' := by
  subst U'
  exact LinearEquiv.refl ℂ _

@[simp]
private theorem coefficientSubgroupCongr_mk (ρ : Representation ℂ (B.Levi F) V)
    {U U' : Subgroup (B.Levi F)} (h : U = U') (v : V) :
    coefficientSubgroupCongr F B ρ h (Jacquet.mk ρ U v) =
      Jacquet.mk ρ U' v := by
  subst U'
  rfl

end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F) B C w S)

include S hS in
/-- The genuine source induction character is trivial on the actual source
radical intersection, using the supplied unipotent refinement equality. -/
theorem sourceUnipotent_le_ker_leviHalfModulus :
    sourceUnipotent F B C w ≤ (T.leviHalfModulus B).ker := by
  intro u hu
  have hr : u ∈ refinedUnipotent F B S := hS.2.2 ▸ hu
  exact T.leviHalfModulus_refinedUnipotent B S ⟨u, hr⟩

/-- The actual positive-half inducing coefficient has exactly the refined
source Jacquet carrier as its radical quotient. -/
def parabolicOrbitRefinedCoefficientEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) :
    Jacquet.Coinvariants
        (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B) ρ)
        (parabolicOrbitCoefficientRadical F B C w) ≃ₗ[ℂ]
      RefinedJacquetModule B S ρ := by
  exact (parabolicOrbitCoefficientEquiv F B C w (T.leviHalfModulus B) ρ
    (T.sourceUnipotent_le_ker_leviHalfModulus B C w S hS)).trans
      (coefficientSubgroupCongr F B ρ hS.2.2)

@[simp]
theorem parabolicOrbitRefinedCoefficientEquiv_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) (v : V) :
    T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (Jacquet.mk
          (parabolicOrbitCoefficient F B C w (T.leviHalfModulus B) ρ)
          (parabolicOrbitCoefficientRadical F B C w) v) =
      refinedJacquetMk B S ρ v := by
  simp only [parabolicOrbitRefinedCoefficientEquiv, LinearEquiv.trans_apply,
    parabolicOrbitCoefficientEquiv_mk, coefficientSubgroupCongr_mk]

end Langlands.LocalFieldData
