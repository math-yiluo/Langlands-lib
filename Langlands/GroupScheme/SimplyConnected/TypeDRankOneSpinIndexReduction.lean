import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationStatement
import Langlands.GroupScheme.SimplyConnected.TypeDRankOneSpinStatement

/-!
# The rank-one type-D identification from a classical spin presentation

The classification prerequisite remains an explicit hypothesis. The proof
extracts division degree two and the required number of quaternionic variables
from the distinguished vertex and the split rank.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem rankOne_spin_of_numbering
    (hclass : ClassicalTypeDSpinPresentationStatement.{u})
    {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n) (hn : 4 ≤ n)
    (hsc : IsSimplyConnected G) (ha : IsAbsolutelyAlmostSimple G)
    (he : d.IsNumberingOf (CartanMatrix.D n) (fun i => i.val = 1) e)
    (hstar : ∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a)
    (hrank : splitRank G = 1) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
      Module.finrank K D = 4 ∧
        ∃ σ : Quaternionic.FirstKindInvolution K D,
          Module.finrank K σ.symmetricSubspace = 3 ∧
            ∃ q : σ.QuadraticForms (Fin n),
              σ.IsNondegenerateQuadratic q ∧ σ.quadraticWittIndex q = 1 ∧
                ∃ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π := by
  obtain ⟨D, iD, iKD, iC, iFD, degree, m, hdegree, hD, hm,
    σ, hσ, q, hq, hwitt, hmarked, π, hπ⟩ :=
    hclass K G d n e hn hsc ha he.1 hstar
  have hwitt1 : σ.quadraticWittIndex q = 1 :=
    ENat.natCast_inj.mp (by simpa using hwitt.trans hrank)
  let vertex : d.Vertex := e.symm ⟨1, by omega⟩
  have hvertex : (e vertex).val = 1 := by simp [vertex]
  have hdist : vertex ∈ d.distinguishedVertices := (he.2 vertex).2 hvertex
  obtain ⟨j, hjpos, hjle, hjdegree⟩ :=
    (hmarked vertex (by omega)).1 hdist
  have hj : j = 1 := by omega
  have hdegree2 : degree = 2 := by simpa [hvertex, hj] using hjdegree.symm
  have hmn : m = n := by
    rw [hdegree2] at hm
    omega
  subst degree
  subst m
  exact ⟨D, iD, iKD, iC, iFD, hD, σ, hσ, q, hq, hwitt1, π, hπ⟩

/-- The general classical type-D spin classification, including its aligned
index comparisons, implies the exact rank-one outer-D4/inner-D5 target.
The general classification is an explicit, unproved input. -/
theorem typeDRankOneSpin_of_classicalTypeDSpinPresentation
    (hclass : ClassicalTypeDSpinPresentationStatement.{u}) :
    TypeDRankOneSpinStatement.{u} := by
  intro K _ G _ _ d n hsc ha hindex hrank
  rcases hindex with ⟨rfl, e, he, hpair⟩ | ⟨rfl, ⟨e, he⟩, htrivial⟩
  · apply rankOne_spin_of_numbering hclass G d 4 e (by omega) hsc ha he _ hrank
    intro γ a hchain
    apply e.injective
    rcases hpair.2.1 γ with hfix | hswap
    · exact hfix a
    · rw [hswap a]
      apply Equiv.swap_apply_of_ne_of_ne <;>
        intro h <;> have := congrArg Fin.val h <;> omega
  · apply rankOne_spin_of_numbering hclass G d 5 e (by omega) hsc ha he _ hrank
    intro γ a _
    exact htrivial γ a

end Langlands.GroupScheme
