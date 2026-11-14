import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllFieldBZ.Representation.Geometric.StandardIntersectionsProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementCharacter
import Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
universe uF uV uW

variable (F : Type uF) [CommRing F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

private def _root_.Langlands.Geometric.coefficientSubgroupCongr (ρ : Representation ℂ (B.Levi F) V)
    {U U' : Subgroup (B.Levi F)} (h : U = U') :
    Jacquet.Coinvariants ρ U ≃ₗ[ℂ] Jacquet.Coinvariants ρ U' := by
  subst U'
  exact LinearEquiv.refl ℂ _

@[simp]
private theorem _root_.Langlands.Geometric.coefficientSubgroupCongr_mk (ρ : Representation ℂ (B.Levi F) V)
    {U U' : Subgroup (B.Levi F)} (h : U = U') (v : V) :
    coefficientSubgroupCongr F B ρ h (Jacquet.mk ρ U v) =
      Jacquet.mk ρ U' v := by
  subst U'
  rfl

end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)

include S hS in
/-- The genuine source induction character is trivial on the actual source
radical intersection, using the supplied unipotent refinement equality. -/
theorem sourceUnipotent_le_ker_leviHalfModulus :
    sourceUnipotent F.Carrier B C w ≤ (T.leviHalfModulus B).ker := by
  intro u hu
  have hr : u ∈ refinedUnipotent F.Carrier B S := hS.2.2 ▸ hu
  exact T.leviHalfModulus_refinedUnipotent B S ⟨u, hr⟩

/-- The actual positive-half inducing coefficient has exactly the refined
source Jacquet carrier as its radical quotient. -/
def parabolicOrbitRefinedCoefficientEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Jacquet.Coinvariants
        (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
        (parabolicOrbitCoefficientRadical F.Carrier B C w) ≃ₗ[ℂ]
      RefinedJacquetModule B S ρ := by
  exact (parabolicOrbitCoefficientEquiv F.Carrier B C w (T.leviHalfModulus B) ρ
    (T.sourceUnipotent_le_ker_leviHalfModulus B C w S hS)).trans
      (coefficientSubgroupCongr F.Carrier B ρ hS.2.2)

@[simp]
theorem parabolicOrbitRefinedCoefficientEquiv_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ
        (Jacquet.mk
          (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
          (parabolicOrbitCoefficientRadical F.Carrier B C w) v) =
      refinedJacquetMk B S ρ v := by
  simp only [parabolicOrbitRefinedCoefficientEquiv, LinearEquiv.trans_apply,
    parabolicOrbitCoefficientEquiv_mk, coefficientSubgroupCongr_mk]

@[simp]
theorem parabolicOrbitRefinedCoefficientEquiv_symm_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ).symm
        (refinedJacquetMk B S ρ v) =
      Jacquet.mk
        (parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B) ρ)
        (parabolicOrbitCoefficientRadical F.Carrier B C w) v := by
  apply (T.parabolicOrbitRefinedCoefficientEquiv B C w S hS ρ).injective
  rw [LinearEquiv.apply_symm_apply, parabolicOrbitRefinedCoefficientEquiv_mk]

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
