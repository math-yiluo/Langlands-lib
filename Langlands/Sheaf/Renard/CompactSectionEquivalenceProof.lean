import Langlands.Sheaf.Renard.SheafComparisonIsIsoProof
import Langlands.Sheaf.Renard.ModuleProjectorComparisonProof

/-!
# Proof: Renard's II.2.5 Theorem, the compact-section functor is an equivalence

Renard (9 July 2026), II.2.5 Theorem and its proof, printed pp.39–40 / PDF pp.45–46:
`M ↦ M_c(X)` is an equivalence between sheaves of `C^∞_X`-modules and nondegenerate
`D(X)`-modules, with inverse `M ↦ (U ↦ χ_U · M)`. The published comparisons
`F ⟶ P(Γc F)` and `M ⟶ Γc(P M)` are natural isomorphisms, so they are the unit and the
(inverse of the) counit of an equivalence whose functor is the compact-section functor.
-/

namespace Langlands.Sheaf.Renard.CompactSectionEquivalence

open CategoryTheory
open Langlands.Algebra Langlands.HarmonicAnalysis

variable {X : Type} [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)

/-- The equivalence of categories built from the two comparison isomorphisms: functor
`compactSectionFunctor hX`, inverse `ProjectorVectorSheaf.functor hX`, unit the sheaf-side
comparison and counit the inverse of the module-side comparison. -/
noncomputable def equivalenceOfComparisons
    [IsIso (SheafProjectorComparison.sheafComparisonNat hX)]
    [IsIso (ModuleProjectorComparison.moduleComparisonNat hX)] :
    VectorSheafScalars.VectorSheaf X ≌
      NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X) :=
  CategoryTheory.Equivalence.mk (CompactSectionTestModule.compactSectionFunctor hX)
    (ProjectorVectorSheaf.functor.{0, 0} hX)
    (asIso (SheafProjectorComparison.sheafComparisonNat hX))
    (asIso (ModuleProjectorComparison.moduleComparisonNat hX)).symm

/-- The functor of `equivalenceOfComparisons` is the compact-section functor. -/
theorem equivalenceOfComparisons_functor
    [IsIso (SheafProjectorComparison.sheafComparisonNat hX)]
    [IsIso (ModuleProjectorComparison.moduleComparisonNat hX)] :
    (equivalenceOfComparisons hX).functor = CompactSectionTestModule.compactSectionFunctor hX :=
  rfl

/-- If every sheaf-side and every module-side comparison is an isomorphism, the
compact-section functor is an equivalence. -/
theorem compactSectionFunctorIsEquivalence_of_comparisons
    (hS : SheafComparisonIsIso) (hM : ModuleProjectorComparison.ModuleComparisonIsIso) :
    CompactSectionFunctorIsEquivalence := by
  intro X _ hX
  have : ∀ F, IsIso ((SheafProjectorComparison.sheafComparisonNat hX).app F) :=
    fun F => hS X hX F
  have : ∀ M, IsIso ((ModuleProjectorComparison.moduleComparisonNat hX).app M) :=
    fun M => hM X hX M
  have : IsIso (SheafProjectorComparison.sheafComparisonNat hX) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (ModuleProjectorComparison.moduleComparisonNat hX) :=
    NatIso.isIso_of_isIso_app _
  exact (equivalenceOfComparisons hX).isEquivalence_functor

/-- Renard II.2.5 Theorem: for every t.d. space `X`, the compact-section functor
`F ↦ F_c(X)` from complex vector sheaves to nondegenerate `D(X)`-modules is an
equivalence of categories. -/
theorem compactSectionFunctorIsEquivalence : CompactSectionFunctorIsEquivalence :=
  compactSectionFunctorIsEquivalence_of_comparisons sheafComparisonIsIso
    ModuleProjectorComparison.moduleComparisonIsIso

end Langlands.Sheaf.Renard.CompactSectionEquivalence
