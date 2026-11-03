import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyReduction
import Langlands.GroupScheme.Absolute.BorelMaximalTorusStatement

/-! # Maximal tori and Borel subgroups, assuming Borel conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]

namespace BorelExistence

/-- A closed torus is an admissible subgroup: it is smooth, connected and solvable. -/
theorem isAdmissible_of_isTorus {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
    (hj : IsClosedSubgroup j) : IsAdmissible j :=
  ⟨hj, hT.smooth, hT.connectedSpace, isSolvableGroupScheme_of_commutative⟩

end BorelExistence

open BorelExistence

/-- Every maximal torus lies in a Borel subgroup, over any field. -/
theorem maximalToriLieInBorels (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] : MaximalToriLieInBorels G := by
  intro T j hj
  obtain ⟨B, i, f, hi, hf⟩ :=
    exists_isBorelSubgroup_containing j (isAdmissible_of_isTorus j hj.1 hj.2.1)
  exact ⟨B, i, hi, hj, f, hf⟩

/-- Some maximal torus of the ambient group lies in a Borel subgroup, over any field. -/
theorem exists_isBorelPair (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsBorelPair i j := by
  obtain ⟨T, j, hj⟩ := exists_isMaximalTorus G
  obtain ⟨B, i, hij⟩ := maximalToriLieInBorels G T j hj
  exact ⟨B, i, T, j, hij⟩

/-- A Borel pair can be transported along a conjugation of its Borel subgroup. -/
theorem IsBorelPair.of_subgroupConjugate {G B B' : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G} {j : T.toGrp ⟶ G}
    (h : IsBorelPair i j) (i' : B' ⟶ G) (hi' : IsBorelSubgroup i')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : B ≅ B')
    (hφ : i ≫ (G.innerIso g).hom = φ.hom ≫ i') :
    IsBorelPair i' (j ≫ (G.innerIso g).hom) := by
  obtain ⟨-, hj, f, hf⟩ := h
  refine ⟨hi', hj.comp_iso _, f ≫ φ.hom, ?_⟩
  rw [Category.assoc, ← hφ, ← Category.assoc, hf]

/-- Every Borel subgroup of `G` contains a maximal torus of `G`. -/
def BorelSubgroupsContainMaximalTori (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsBorelPair i j

/-- If any two Borel subgroups of `G` are conjugate by a rational point, then every Borel
subgroup of `G` contains a maximal torus of `G`. -/
theorem BorelSubgroupsContainMaximalTori.of_conjugate (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hconj : ∀ (B B' : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (i' : B' ⟶ G),
      IsBorelSubgroup i → IsBorelSubgroup i' →
        ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : B ≅ B'),
          i ≫ (G.innerIso g).hom = φ.hom ≫ i') :
    BorelSubgroupsContainMaximalTori G := by
  intro B i hi
  obtain ⟨B₀, i₀, T, j, hij⟩ := exists_isBorelPair G
  obtain ⟨g, φ, hφ⟩ := hconj B₀ B i₀ i hij.1 hi
  exact ⟨T, j ≫ (G.innerIso g).hom, hij.of_subgroupConjugate i hi g φ hφ⟩

end Field

/-- Borel conjugacy implies that every Borel subgroup contains a maximal torus of the ambient
group (Milne, the paragraph after Definition 17.12). -/
theorem borelMaximalTorusStatement_of_borelConjugacy (hconj : BorelConjugacyStatement.{u}) :
    BorelMaximalTorusStatement.{u} := by
  intro k _ _ G _ _ _
  exact BorelSubgroupsContainMaximalTori.of_conjugate G (hconj k G).2

/-- Maximal-torus conjugacy follows from Borel conjugacy and conjugacy of maximal tori in
smooth connected solvable groups; the containment input is `maximalToriLieInBorels`. -/
theorem maximalTorusConjugacyStatement_of_borelConjugacy
    (hBorel : BorelConjugacyStatement.{u})
    (hsolvable : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (B : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left],
      IsSolvableGroupScheme B → MaximalToriAreConjugate B) :
    MaximalTorusConjugacyStatement.{u} :=
  maximalTorusConjugacyStatement_of_borel_inputs hBorel
    (fun _ _ _ G _ _ _ => maximalToriLieInBorels G) hsolvable

end Langlands.GroupScheme
