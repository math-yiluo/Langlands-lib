import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.Representation.Plancherel.RenardUniformizerSection
import Mathlib.GroupTheory.DoubleCoset

/-! # Dominant Cartan representatives for the standard integral subgroup of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel.RenardCartan
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.SpecialCompact

/-- The positive uniformizer points give exactly one representative of each
double coset for the standard integral subgroup of `GL_N`. -/
def GeneralLinearIntegralCartanStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N)))),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
    IsGenericCocharacter i ν →
      Function.Bijective (fun a : C0Plus _ i (positiveRelativeRoots i ν) =>
        DoubleCoset.mk K K a.val)

end Langlands.BruhatTits.SpecialCompact
