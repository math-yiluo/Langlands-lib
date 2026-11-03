import Langlands.GroupScheme.Absolute.SmoothSubgroupPointComparison
import Langlands.GroupScheme.Rational.StandardParabolicPointsStatement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement

/-! # Smooth closed overgroups from standard rational-point classification -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- An actual standard cocharacter of the specified torus presenting the given
smooth closed overgroup on every test scheme. -/
structure StandardDynamicOvergroupData (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (i : P ⟶ G) where
  index : Set (characterLattice T)
  subset : index ⊆ simpleRelativeRoots j ν
  cocharacter : cocharacterLattice T
  standard : IsStandardCocharacter j ν index cocharacter
  range_eq : SubgroupFunctor.range i =
    Dynamic.parabolic (CommGroupScheme.groupHom cocharacter ≫ j)

section AlgClosed

variable [IsAlgClosed k] [Smooth G.X.hom] [Smooth P.X.hom]
  (j : T.toGrp ⟶ G) (ν : cocharacterLattice T) (i : P ⟶ G)

/-- The overgroup clause on field points and actual standard cocharacters
suffice for all-test classification of smooth closed overgroups. -/
theorem nonempty_standardDynamicOvergroupData_of_points
    (hi : IsClosedSubgroup i)
    (hclass : ∀ H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤ H →
        ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots j ν ∧
          H = standardParabolicPoints j ν J)
    (hstandard : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots j ν →
      ∃ ζ : cocharacterLattice T, IsStandardCocharacter j ν J ζ ∧
        standardParabolic j ν J =
          Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j))
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ≤
      SubgroupFunctor.range i) :
    Nonempty (StandardDynamicOvergroupData j ν i) := by
  obtain ⟨J, hJ, hpoints⟩ := hclass
    ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hle _)
  obtain ⟨ζ, hζ, heq⟩ := hstandard J hJ
  refine ⟨⟨J, hJ, ζ, hζ, ?_⟩⟩
  apply (Dynamic.range_eq_parabolic_iff_algClosed_points
    (CommGroupScheme.groupHom ζ ≫ j) hi).mpr
  exact hpoints.trans (congrArg
    (fun F : SubgroupFunctor G =>
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) heq)

/-- Global rational structural statements supply the two explicit local
classification inputs. No proof of those statements is asserted here. -/
def standardDynamicOvergroupData_of_statements
    (hpoints : StandardParabolicPointsStatement.{u})
    (hstandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hj : IsMaximalSplitTorus j)
    (hν : IsGenericCocharacter j ν) (hi : IsClosedSubgroup i)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ≤
      SubgroupFunctor.range i) : StandardDynamicOvergroupData j ν i := by
  apply Classical.choice
  apply nonempty_standardDynamicOvergroupData_of_points j ν i hi
  · intro H hH
    exact ((hpoints k G hG T j hj ν hν).2.1 H).mp hH
  · intro J hJ
    obtain ⟨hex, hall⟩ := hstandard k G hG T j hj ν hν J hJ
    obtain ⟨ζ, hζ⟩ := hex
    exact ⟨ζ, hζ, (hall ζ hζ).1⟩
  · exact hle

end AlgClosed

end Langlands.GroupScheme
