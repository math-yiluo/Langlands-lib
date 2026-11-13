import Langlands.Global.AdelicRankOneOrbitHeightBound

/-! # Statement: the arithmetic rank-one height bound for split groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme

/-- The split case of `RankOneParabolicRationalOrbitHeightBoundStatement`: the same
uniform rational-orbit height bound on ambient norm-one adelic points, for actual
connected reductive groups of semisimple relative rank one whose given maximal split
torus is also a maximal torus. -/
def SplitRankOneParabolicRationalOrbitHeightBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i → IsMaximalTorus i →
          ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
            ∀ α : characterLattice T, simpleRelativeRoots i ν = {α} →
              ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (j : Fin n),
                ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) j →
                  HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)

/-- The general rank-one statement specializes to its split case. -/
theorem splitRankOneParabolicRationalOrbitHeightBound_of_rankOne
    (h : RankOneParabolicRationalOrbitHeightBoundStatement.{u}) :
    SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u} :=
  fun F _ _ G _ _ hG T i hi _ ν hν α hα n ρ j hstab => h F G hG T i hi ν hν α hα n ρ j hstab

end Langlands.Global.RepresentationGrowth
