import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitCoefficientComparison
import Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient` to an arbitrary nonarchimedean local field
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

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
open Langlands.Induction
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual nested positive-half coefficient quotient is the refined Jacquet carrier. -/
def parabolicOrbitNestedRefinedCoefficientEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation.Coinvariants
        (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) ≃ₗ[ℂ]
      RefinedJacquetModule B S ρ :=
  (splitStagesCoefficientEquiv (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier) (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w) (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)).trans
      (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ)

@[simp] theorem parabolicOrbitNestedRefinedCoefficientEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) v) =
      refinedJacquetMk B S ρ v :=
  T.parabolicOrbitRefinedCoefficientEquiv_mk B C w S hS ρ v

@[simp] theorem parabolicOrbitNestedRefinedCoefficientEquiv_symm_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ).symm
        (refinedJacquetMk B S ρ v) =
      Representation.Coinvariants.mk
        (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) v := by
  apply (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ).injective
  rw [LinearEquiv.apply_symm_apply, parabolicOrbitNestedRefinedCoefficientEquiv_mk]

/-- The nested refined quotient comparison commutes with every normalized Jacquet map. -/
theorem parabolicOrbitNestedRefinedCoefficientEquiv_natural
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ)
    (z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)) :
    T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS τ
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F.Carrier B C w (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS ρ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    change T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS τ
      (Representation.Coinvariants.mk _ (f v)) = _
    rw [parabolicOrbitNestedRefinedCoefficientEquiv_mk,
      parabolicOrbitNestedRefinedCoefficientEquiv_mk]
    rfl

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
