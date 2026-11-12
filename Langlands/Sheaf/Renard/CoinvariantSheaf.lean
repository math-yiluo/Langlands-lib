import Langlands.Sheaf.Renard.CompactSectionActions
import Langlands.Sheaf.Renard.CoinvariantTestModule
import Langlands.Sheaf.Renard.ModuleProjectorComparison

/-!
# The actual coinvariant sheaf along an invariant map

Renard III.3.1 reconstructs the ordinary vector sheaf on Y from the
original nondegenerate target-test module of compact-section coinvariants.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.CoinvariantSheaf

open CategoryTheory
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.VectorSheafScalars

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [ContinuousSMul G X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)
variable (q : C(X, Y)) (hq : ∀ (g : G) (x : X), q (g • x) = q x)
variable (hY : Langlands.Topology.IsLocallyProfinite Y)

/-- The original target-test module before taking compact-section coinvariants. -/
def sourceModules :
    ActionSheaf G X ⥤ NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier Y) :=
  CompactSectionActions.functor hX ⋙ CoinvariantTestModule.sourceFunctor q hY

/-- The original nondegenerate module of compact-section coinvariants. -/
def modules :
    ActionSheaf G X ⥤ NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier Y) :=
  CompactSectionActions.functor hX ⋙ CoinvariantTestModule.functor q hq hY

/-- The literal quotient maps form a natural transformation of original target-test modules. -/
def quotient : sourceModules (G := G) hX q hY ⟶ modules hX q hq hY :=
  Functor.whiskerLeft (CompactSectionActions.functor hX)
    (CoinvariantTestModule.quotient q hq hY)

/-- Renard's sheaf F-prime, on the actual ordinary complex vector-sheaf category of Y. -/
def functor : ActionSheaf G X ⥤ VectorSheaf Y :=
  modules hX q hq hY ⋙ ProjectorVectorSheaf.functor hY

/-- The canonical original-module comparison from coinvariants to compact sections of F-prime. -/
def compactComparison :
    modules hX q hq hY ⟶ functor hX q hq hY ⋙
      CompactSectionTestModule.compactSectionFunctor hY :=
  Functor.whiskerLeft (modules hX q hq hY)
    (ModuleProjectorComparison.moduleComparisonNat hY)

/-- The original quotient followed by the canonical compact-section comparison. -/
def compactQuotient :
    sourceModules (G := G) hX q hY ⟶ functor hX q hq hY ⋙
      CompactSectionTestModule.compactSectionFunctor hY :=
  quotient hX q hq hY ≫ compactComparison hX q hq hY

/-- The underlying sheaf is the published projector sheaf of the actual coinvariant module. -/
theorem functor_obj (F : ActionSheaf G X) :
    (functor hX q hq hY).obj F =
      ProjectorVectorSheaf.sheaf hY ((modules hX q hq hY).obj F).property := rfl

/-- The source quotient is the literal original representation-coinvariant quotient. -/
theorem quotient_apply (F : ActionSheaf G X)
    (s : CompactSupport.submodule
      (Langlands.Sheaf.Equivariant.CompactSections.ordinary F.obj)) :
    letI : Module ℂ (CompactSectionActions.moduleObject hX F).obj :=
      NondegenerateScalars.module ℂ PointwiseTestAlgebra.isIdempotented
        (CompactSectionActions.moduleObject hX F).property
    CompatibleTestActions.CompatibleTestAction.moduleMap ((quotient hX q hq hY).app F) s =
      Representation.Coinvariants.mk (CompactSectionActions.canonicalAction hX F) s := rfl

/-- The compact-section quotient kills every original group-action difference. -/
theorem compactQuotient_action (F : ActionSheaf G X) (g : G)
    (s : CompactSupport.submodule
      (Langlands.Sheaf.Equivariant.CompactSections.ordinary F.obj)) :
    CompatibleTestActions.CompatibleTestAction.moduleMap
        ((compactQuotient hX q hq hY).app F) (compactRepresentation F g s) =
      CompatibleTestActions.CompatibleTestAction.moduleMap
        ((compactQuotient hX q hq hY).app F) s := by
  apply congrArg
    (CompatibleTestActions.CompatibleTestAction.moduleMap
      ((compactComparison hX q hq hY).app F))
    (CoinvariantTestModule.quotientMap_action q hq hY
      (CompactSectionActions.compatibleObject hX F) g s)

end Langlands.Sheaf.Renard.CoinvariantSheaf
