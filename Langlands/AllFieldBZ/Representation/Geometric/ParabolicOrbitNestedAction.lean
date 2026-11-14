import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitSectionComparison
import Langlands.AllFieldBZ.Representation.Induction.InverseTranspose
import Langlands.Representation.Geometric.ParabolicOrbitNestedAction

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitNestedAction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitNestedAction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
open Langlands.Induction
universe uF uV uW

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

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

/-- The action on the actual nested quotient is projected normalized refined
Jacquet with the two explicit positive source half moduli. -/
def parabolicOrbitNestedRefinedCoefficientActionEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (parabolicOrbitNestedCoefficientAction F.Carrier B C w (T.leviHalfModulus B) ρ).Equiv
      (twist (T.parabolicOrbitSectionCharacter B C w S R hS hR)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (parabolicOrbitSourceRefinedCoordinate F.Carrier B C w R hR S hS))) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact (parabolicOrbitNestedFullCoefficientActionEquiv F.Carrier B C w
    (T.leviHalfModulus B) ρ).trans
      (T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ)

@[simp] theorem parabolicOrbitNestedRefinedCoefficientActionEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR ρ
        (Representation.Coinvariants.mk
          (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ) v) =
      refinedJacquetMk B S ρ v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change T.parabolicOrbitFullRefinedCoefficientActionEquiv B C w S R hS hR ρ
    (Jacquet.mk _ _ v) = _
  exact T.parabolicOrbitFullRefinedCoefficientActionEquiv_mk B C w S R hS hR ρ v

/-- The normalized action equivalence is natural for all original coefficient maps. -/
theorem parabolicOrbitNestedRefinedCoefficientActionEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ z : Representation.Coinvariants
      (parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ),
    T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR τ
        (Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F.Carrier B C w (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedJacquetMap B S f
        (T.parabolicOrbitNestedRefinedCoefficientActionEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact T.parabolicOrbitNestedRefinedCoefficientEquiv_natural B C w S hS f

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
