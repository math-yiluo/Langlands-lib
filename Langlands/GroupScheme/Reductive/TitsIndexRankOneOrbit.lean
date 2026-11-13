import Langlands.GroupScheme.Reductive.TitsIndexSplitRankProof

/-! # The distinguished orbit of an actual rank-one Tits index

Split rank one gives exactly one orbit for the full absolute Galois star
action on distinguished vertices. We choose an actual vertex in that orbit
and characterize its orbit without passing to a finite Galois quotient. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- At split rank one the actual distinguished-orbit quotient has one element. -/
theorem card_distinguishedOrbit_eq_one (hrank : splitRank G = 1) :
    Nat.card d.DistinguishedOrbit = 1 :=
  ENat.natCast_inj.mp (by simpa [hrank] using (titsIndexSplitRank k G d).1)

/-- Every pair of distinguished vertices is related by the actual star action
of one element of the full absolute Galois group. -/
theorem exists_star_eq_of_rank_one (hrank : splitRank G = 1)
    (a b : d.distinguishedVertices) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a.val = b.val := by
  have : Subsingleton d.DistinguishedOrbit :=
    (Nat.card_eq_one_iff_unique.mp (d.card_distinguishedOrbit_eq_one hrank)).1
  exact Quotient.exact (Subsingleton.elim (d.orbitClass a) (d.orbitClass b))

/-- A chosen actual distinguished simple vertex at split rank one. -/
def rankOneDistinguishedVertex (hrank : splitRank G = 1) : d.distinguishedVertices :=
  (Classical.choice
    (Nat.card_eq_one_iff_unique.mp (d.card_distinguishedOrbit_eq_one hrank)).2).out

/-- The distinguished set is exactly the full star orbit of the chosen vertex. -/
theorem mem_distinguishedVertices_iff_rankOne_orbit (hrank : splitRank G = 1)
    (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔
      ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        d.star σ (d.rankOneDistinguishedVertex hrank).val = a := by
  constructor
  · intro ha
    exact d.exists_star_eq_of_rank_one hrank (d.rankOneDistinguishedVertex hrank) ⟨a, ha⟩
  · rintro ⟨σ, rfl⟩
    change d.star σ (d.rankOneDistinguishedVertex hrank).val ∉ d.zeroVertices
    exact fun h => (d.rankOneDistinguishedVertex hrank).property
      ((titsIndexStarInvariant k G d σ _).mp h)

/-- All distinguished simple roots have the same actual nonzero restriction. -/
theorem rootRestriction_eq_of_rank_one (hrank : splitRank G = 1)
    (a b : d.distinguishedVertices) :
    d.rootRestriction a.val.val = d.rootRestriction b.val.val :=
  (titsIndexRelativeSimpleRoots k G d).1 a b |>.mpr
    (d.exists_star_eq_of_rank_one hrank a b)

/-- If the full star action is trivial, the chosen vertex is the unique
distinguished vertex at split rank one. -/
theorem distinguishedVertices_eq_singleton_of_star_trivial
    (hrank : splitRank G = 1)
    (hstar : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex),
      d.star σ a = a) :
    d.distinguishedVertices = {(d.rankOneDistinguishedVertex hrank).val} := by
  ext a
  rw [d.mem_distinguishedVertices_iff_rankOne_orbit hrank]
  constructor
  · rintro ⟨σ, hσ⟩
    exact (hstar σ _).symm.trans hσ |>.symm
  · intro ha
    exact ⟨1, by simpa using ha.symm⟩

end Langlands.GroupScheme.TitsIndexData
