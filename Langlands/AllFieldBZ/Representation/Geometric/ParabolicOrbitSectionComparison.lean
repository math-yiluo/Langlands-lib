import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitStagesCoefficient
import Langlands.Representation.Geometric.ParabolicOrbitSectionComparison

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitSectionComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitSectionComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
open Langlands.Induction
universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (R : BlockRefinement C)
  (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Topology
variable [TopologicalSpace F]

variable [IsTopologicalRing F]

end Topology
end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
open Langlands.Induction
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The two source positive halves retained before the Haar and target corrections. -/
def parabolicOrbitSectionCharacter :
    parabolicOrbitStagesQuotient F.Carrier B C w →* ℂˣ :=
  (T.leviHalfModulus B).comp
      ((sourceLevi F.Carrier B C w).subtype.comp
        (parabolicOrbitSourceLeviCoordinate F.Carrier B C w R hR)) *
    (T.refinedLeviHalfModulus B S).comp
      (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS)

private theorem sectionCharacter_normalized_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (l : parabolicOrbitStagesQuotient F.Carrier B C w) (v : V) :
    (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS l)
          (refinedJacquetMk B S ρ v) =
      (T.leviHalfModulus B
        (parabolicOrbitSourceLeviCoordinate F.Carrier B C w R hR l).val : ℂ) •
        refinedJacquetMk B S ρ
          (ρ (parabolicOrbitSourceLeviCoordinate F.Carrier B C w R hR l).val v) := by
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
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    (parabolicOrbitFullCoefficientAction F.Carrier B C w (T.leviHalfModulus B) ρ).Equiv
      (twist (T.parabolicOrbitSectionCharacter B C w S R hS hR)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS))) where
  toLinearEquiv := T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (Jacquet.mk _ _ ((twist (T.leviHalfModulus B) ρ)
          (parabolicOrbitToSourceLevi F.Carrier B C w
            (parabolicOrbitStagesSection F.Carrier B C w l)) v)) =
      (T.parabolicOrbitSectionCharacter B C w S R hS hR l : ℂ) •
        T.normalizedRefinedJacquet B S ρ
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS l)
          (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ (Jacquet.mk _ _ v))
    rw [T.parabolicOrbitRefinedCoefficientEquiv_mk,
      T.parabolicOrbitRefinedCoefficientEquiv_mk,
      parabolicOrbitToSourceLevi_stagesSection F.Carrier B C w R hR,
      sectionCharacter_normalized_mk]
    exact map_smul (refinedJacquetMk B S ρ) _ _

@[simp] theorem parabolicOrbitFullRefinedCoefficientActionEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ
        (Jacquet.mk _ (parabolicOrbitCoefficientRadical F.Carrier B C w) v) =
      refinedJacquetMk B S ρ v :=
  T.parabolicOrbitRefinedCoefficientEquiv_mk B C w S hS ρ v

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
