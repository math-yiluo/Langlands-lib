import Langlands.Representation.Category.Basic
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RepresentationTheory.Semisimple

/-!
# Renard VI.3.2(ii): finite semisimple restriction to the actual norm kernel

A statement only: no proof is given here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV

/-- Renard VI.3.2(ii) with its finite spanning-family consequence: the restriction of
an irreducible smooth complex representation of the rational points of a connected
reductive group to the actual common rational-character norm kernel is semisimple,
has finite length over the subgroup group algebra, and is spanned by finitely many
irreducible subrepresentations. -/
def RationalNormKernelFiniteRestrictionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G),
      π.IsIrreducible →
      let H := Plancherel.rationalCommonNormKernel G
      let ρH : Representation ℂ H π := π.representation.comp H.subtype
      Representation.IsSemisimpleRepresentation ρH ∧
      IsFiniteLength (MonoidAlgebra ℂ H) ρH.asModule ∧
      ∃ (m : ℕ) (W : Fin m → Subrepresentation ρH),
        (∀ i, Representation.IsIrreducible (W i).toRepresentation) ∧
        (⨆ i, (W i).toSubmodule) = ⊤

end Langlands.CuspidalSupport
