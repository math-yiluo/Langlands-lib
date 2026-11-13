import Langlands.Sheaf.Renard.SheafComparisonIsIsoProof
import Langlands.Sheaf.Renard.ModuleProjectorComparisonProof

/-!
# The projector sheaf functor is an equivalence

Renard (9 July 2026), II.2.5 Theorem, printed p.39 / PDF p.45, with its proof on printed
pp.39–40 / PDF pp.45–46: the functor `M ↦ (U ↦ χ_U · M)` from nondegenerate `D(X)`-modules
to complex vector sheaves is an equivalence, inverse to `F ↦ F_c(X)`. The two published
comparison isomorphisms make the comparison natural transformations the supplied unit and
counit isomorphisms passed to `CategoryTheory.Equivalence.mk`, which keeps the counit and
adjusts the unit to `adjointifyη`; the functor of the resulting equivalence is the
projector functor.
-/

namespace Langlands.Sheaf.Renard.CompactSectionEquivalence

open CategoryTheory

/-- The two comparison isomorphisms of Renard II.2.5 make the projector functor an
equivalence. The module comparison is the supplied unit isomorphism `η` and the inverse of
the sheaf comparison is the supplied counit isomorphism `ε` of `CategoryTheory.Equivalence.mk`,
which keeps `ε` as the counit and replaces `η` by `adjointifyη η ε`. -/
theorem projectorFunctorIsEquivalence_of_comparisons (hS : SheafComparisonIsIso)
    (hM : ModuleProjectorComparison.ModuleComparisonIsIso) :
    ProjectorFunctorIsEquivalence := by
  intro X _ hX
  have : ∀ M, IsIso ((ModuleProjectorComparison.moduleComparisonNat hX).app M) :=
    fun M => hM X hX M
  have : ∀ F, IsIso ((SheafProjectorComparison.sheafComparisonNat hX).app F) :=
    fun F => hS X hX F
  have : IsIso (ModuleProjectorComparison.moduleComparisonNat hX) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (SheafProjectorComparison.sheafComparisonNat hX) :=
    NatIso.isIso_of_isIso_app _
  exact (CategoryTheory.Equivalence.mk (ProjectorVectorSheaf.functor.{0, 0} hX)
    (CompactSectionTestModule.compactSectionFunctor hX)
    (asIso (ModuleProjectorComparison.moduleComparisonNat hX))
    (asIso (SheafProjectorComparison.sheafComparisonNat hX)).symm).isEquivalence_functor

/-- Renard II.2.5 Theorem: for every t.d. space `X`, the projector functor
`M ↦ (U ↦ χ_U · M)` from nondegenerate test modules to complex vector sheaves is an
equivalence of categories. -/
theorem projectorFunctorIsEquivalence : ProjectorFunctorIsEquivalence :=
  projectorFunctorIsEquivalence_of_comparisons sheafComparisonIsIso
    ModuleProjectorComparison.moduleComparisonIsIso

end Langlands.Sheaf.Renard.CompactSectionEquivalence
