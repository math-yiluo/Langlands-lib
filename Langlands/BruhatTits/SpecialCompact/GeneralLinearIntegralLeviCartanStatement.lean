import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.Representation.Plancherel.RenardUniformizerSection
import Mathlib.GroupTheory.DoubleCoset

/-! # Dominant Cartan representatives in every inherited integral Levi of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Plancherel.RenardCartan
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.SpecialCompact

/-- Positive uniformizer points for the Levi chamber represent the double
cosets of the preimage of the ambient standard integral subgroup. -/
def GeneralLinearIntegralLeviCartanStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N)))),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
    IsGenericCocharacter i ν →
      ∀ J ⊆ simpleRelativeRoots i ν,
        haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
          (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
        let KJ := K.comap (rationalPoints.map (Standard.leviHom i ν J))
        let iJ := Standard.leviTorusHom i ν J
        Function.Bijective (fun a : C0Plus _ iJ (positiveRelativeRoots iJ ν) =>
          DoubleCoset.mk KJ KJ a.val)

end Langlands.BruhatTits.SpecialCompact
