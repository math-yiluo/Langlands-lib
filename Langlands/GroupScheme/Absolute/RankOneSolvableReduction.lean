import Langlands.GroupScheme.Absolute.RankOneSolvableStatement
import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Lie.WeightImage

/-! # Reduction of the rank-one solvable obstruction to Borel subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A property excluding opposite Lie weights for all Borels through `j` excludes
them for every smooth connected solvable closed subgroup through `j`. -/
theorem not_meets_oppositeWeightSpaces_of_borel (j : T.toGrp ⟶ G)
    (hBorel : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
      (t : T.toGrp ⟶ B), IsBorelSubgroup b → t ≫ b = j →
      ∀ α ∈ roots j,
        ¬ (Lie.MeetsWeightSpace j b α ∧ Lie.MeetsWeightSpace j b (-α)))
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (f : T.toGrp ⟶ H) (hi : IsClosedSubgroup i) (hsmooth : Smooth H.X.hom)
    (hconnected : ConnectedSpace H.X.left) (hsolvable : IsSolvableGroupScheme H)
    (hf : f ≫ i = j) (α : characterLattice T) (hα : α ∈ roots j) :
    ¬ (Lie.MeetsWeightSpace j i α ∧ Lie.MeetsWeightSpace j i (-α)) := by
  obtain ⟨B, b, a, hb, ha⟩ :=
    BorelExistence.exists_isBorelSubgroup_containing i
      ⟨hi, hsmooth, hconnected, hsolvable⟩
  have ht : (f ≫ a) ≫ b = j := by
    rw [Category.assoc, ha, hf]
  rintro ⟨hpos, hneg⟩
  exact hBorel B b (f ≫ a) hb ht α hα
    ⟨hpos.of_factorization j i b a ha α,
      hneg.of_factorization j i b a ha (-α)⟩

/-- The exact public obstruction follows from its Borel case over every field.
The hypothesis is retained explicitly; this theorem does not prove that case. -/
theorem rankOneSolvableObstruction_of_borel
    (hBorel : ∀ (k : Type u) [Field k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp → IsMaximalTorus j →
      haveI := hG.isAffineHom
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
        (t : T.toGrp ⟶ B), IsBorelSubgroup b → t ≫ b = j →
        ∀ α ∈ roots j,
          ¬ (Lie.MeetsWeightSpace j b α ∧ Lie.MeetsWeightSpace j b (-α))) :
    RankOneSolvableObstructionStatement.{u} := by
  intro k _ G hG T j hT hj
  have := hG.isAffineHom
  have := hG.smooth
  intro H i f hi hsmooth hconnected hsolvable hf α hα
  exact not_meets_oppositeWeightSpaces_of_borel j
    (hBorel k G hG T j hT hj) H i f hi hsmooth hconnected hsolvable hf α hα

end Langlands.GroupScheme
