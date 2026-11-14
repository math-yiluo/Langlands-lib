import Langlands.Representation.Geometric.ParabolicOrbitSectionComparison
import Langlands.AllField.Representation.Geometric.ParabolicOrbitStagesCoefficient
/-! The full intermediate section factors through the target refined Levi. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.Induction hiding SmoothRep

universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (R : BlockRefinement C)
  (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Topology



end Topology

end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric
open Langlands.Induction hiding SmoothRep

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F) B C w S)
  (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The two source positive halves retained before the Haar and target corrections. -/
def parabolicOrbitSectionCharacter :
    parabolicOrbitStagesQuotient F B C w →* ℂˣ :=
  (T.leviHalfModulus B).comp
      ((sourceLevi F B C w).subtype.comp
        (parabolicOrbitSourceLeviCoordinate F B C w R hR)) *
    (T.refinedLeviHalfModulus B S).comp
      (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS)

private theorem sectionCharacter_normalized_mk
    (ρ : Representation ℂ (B.Levi F) V)
    (l : parabolicOrbitStagesQuotient F B C w) (v : V) :
    (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS l)
          (refinedJacquetMk B S ρ v) =
      (T.leviHalfModulus B
        (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val : ℂ) •
        refinedJacquetMk B S ρ
          (ρ (parabolicOrbitSourceLeviCoordinate F B C w R hR l).val v) := by
  rw [T.normalizedRefinedJacquet_mk]
  simp only [parabolicOrbitSectionCharacter, MonoidHom.mul_apply,
    MonoidHom.comp_apply, Subgroup.coe_subtype, Units.val_mul,
    refinedLeviInverseHalfModulus_eq_inv, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, smul_smul, mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  rfl

/-- The full actual coefficient action identifies with normalized refined Jacquet
action and the two explicit source positive halves. -/
def parabolicOrbitFullRefinedCoefficientActionEquiv
    (ρ : Representation ℂ (B.Levi F) V) :
    (parabolicOrbitFullCoefficientAction F B C w (T.leviHalfModulus B) ρ).Equiv
      (twist (T.parabolicOrbitSectionCharacter B C w S R hS hR)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS))) where
  toLinearEquiv := T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (Jacquet.mk _ _ ((twist (T.leviHalfModulus B) ρ)
          (parabolicOrbitToSourceLevi F B C w
            (parabolicOrbitStagesSection F B C w l)) v)) =
      (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F B C w R hR S hS l)
          (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ (Jacquet.mk _ _ v))
    rw [T.parabolicOrbitRefinedCoefficientEquiv_mk,
      T.parabolicOrbitRefinedCoefficientEquiv_mk,
      parabolicOrbitToSourceLevi_stagesSection F B C w R hR,
      sectionCharacter_normalized_mk]
    exact map_smul (refinedJacquetMk B S ρ) _ _

end Langlands.LocalFieldData
