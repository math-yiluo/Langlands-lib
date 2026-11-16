import Langlands.GroupScheme.SimplyConnected.TypeAOpposition
import Langlands.GroupScheme.SimplyConnected.InnerTypeARankOneProof

/-! # The exact inner-type-A index at split rank one -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

namespace TitsIndexData

/-- A rank-one type-A index with trivial full star action marks precisely the
central position of the chain. -/
theorem rank_one_inner_A_marking (d : TitsIndexData G) {n : ℕ}
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hsc : IsSimplyConnected G) (hrank : splitRank G = 1)
    (hstar : d.StarIsTrivial) (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔ 2 * (e a).val + 1 = n := by
  let v : d.Vertex := (d.rankOneDistinguishedVertex hrank).val
  have hsingle (i : d.Vertex) : i ∈ d.distinguishedVertices ↔ i = v := by
    rw [d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar]
    rfl
  have hv : v ∈ d.distinguishedVertices := (d.rankOneDistinguishedVertex hrank).property
  have hopp : d.opposition v = v :=
    (hsingle _).mp ((d.opposition_mem_distinguished_iff v).mpr hv)
  have hrev := d.opposition_eq_rev_of_A e hA hsc v
  rw [hopp] at hrev
  have hval := congrArg Fin.val hrev
  simp only [Fin.revPerm_apply, Fin.val_rev] at hval
  have hc : 2 * (e v).val + 1 = n := by
    have := (e v).isLt
    omega
  rw [hsingle]
  constructor
  · rintro rfl
    exact hc
  · intro ha
    apply e.injective
    apply Fin.ext
    omega

end TitsIndexData

/-- A binary norm-one model retaining both its division degree and the exact
actual inner-type-A marked index. -/
def IndexedBinaryNormOnePresentation (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) :=
  {p : DegreePreservingBinaryNormOnePresentation K G n //
    d.HasRankOneInnerAIndex (Langlands.CentralSimple.reducedDegree K p.val.divisionAlgebra)}

/-- The actual inner-type-A index has its singleton marked at the degree of
the division algebra in the binary model, over every field. -/
theorem nonempty_indexedBinaryNormOnePresentation
    (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hrank : splitRank G = 1) :
    Nonempty (IndexedBinaryNormOnePresentation K G d n) := by
  let p := innerTypeARankOnePresentation G d n hsc has htype hrank
  have hp := p.property
  have hpos := Langlands.CentralSimple.reducedDegree_pos K p.val.divisionAlgebra
  obtain ⟨_, ⟨e, hA⟩, hstar⟩ := htype
  have hn : n = 2 * Langlands.CentralSimple.reducedDegree K p.val.divisionAlgebra - 1 := by
    omega
  have hmark := d.rank_one_inner_A_marking e hA hsc hrank hstar
  refine ⟨⟨p, hpos, ?_, hstar⟩⟩
  generalize hdegree : Langlands.CentralSimple.reducedDegree K p.val.divisionAlgebra = degree
    at hpos hp hn ⊢
  subst n
  refine ⟨e, hA, ?_⟩
  intro a
  rw [hmark a]
  omega

/-- Choose a binary presentation which also certifies its exact actual index. -/
def innerTypeARankOneIndexedPresentation
    (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hrank : splitRank G = 1) :
    IndexedBinaryNormOnePresentation K G d n :=
  Classical.choice (nonempty_indexedBinaryNormOnePresentation d n hsc has htype hrank)

/-- The complete inner-A alternative of the local enumeration already holds
over an arbitrary field under the actual inner-type-A premise. -/
theorem hasRankOneInnerAIndex_of_hasInnerTypeA
    (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (htype : d.HasInnerTypeA n) (hrank : splitRank G = 1) :
    ∃ degree : ℕ, d.HasRankOneInnerAIndex degree := by
  obtain ⟨p, hp⟩ := innerTypeARankOneIndexedPresentation d n hsc has htype hrank
  exact ⟨Langlands.CentralSimple.reducedDegree K p.val.divisionAlgebra, hp⟩

end Langlands.GroupScheme
