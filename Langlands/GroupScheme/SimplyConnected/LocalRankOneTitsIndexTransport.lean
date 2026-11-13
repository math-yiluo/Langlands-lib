import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement

/-! # Transport of actual local rank-one index alternatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G H J : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  [IsAffineHom J.X.hom] [LocallyOfFiniteType J.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData H} {c : TitsIndexData J}

namespace TitsIndexEquiv

/-- The identity comparison of an actual index. -/
def refl (d : TitsIndexData G) : TitsIndexEquiv d d where
  vertices := Equiv.refl _
  cartan_eq _ _ := rfl
  zero_iff _ := Iff.rfl
  star_eq _ _ := rfl

/-- Reverse an actual index comparison. -/
def symm (f : TitsIndexEquiv d e) : TitsIndexEquiv e d where
  vertices := f.vertices.symm
  cartan_eq a b := by
    simpa using (f.cartan_eq (f.vertices.symm a) (f.vertices.symm b)).symm
  zero_iff a := by
    simpa using (f.zero_iff (f.vertices.symm a)).symm
  star_eq σ a := by
    apply f.vertices.injective
    simpa using (f.star_eq σ (f.vertices.symm a)).symm

/-- Compose comparisons of actual indices over the same field. -/
def trans (f : TitsIndexEquiv d e) (g : TitsIndexEquiv e c) : TitsIndexEquiv d c where
  vertices := f.vertices.trans g.vertices
  cartan_eq a b := (g.cartan_eq (f.vertices a) (f.vertices b)).trans (f.cartan_eq a b)
  zero_iff a := (f.zero_iff a).trans (g.zero_iff (f.vertices a))
  star_eq σ a := by
    change g.vertices (f.vertices (d.star σ a)) = c.star σ (g.vertices (f.vertices a))
    rw [f.star_eq, g.star_eq]

variable (f : TitsIndexEquiv d e)

include f

/-- The complement of the zero vertices is also preserved exactly. -/
theorem distinguished_iff (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔ f.vertices a ∈ e.distinguishedVertices :=
  not_congr (f.zero_iff a)

/-- Transport the same matrix and marked subset along the vertex bijection. -/
theorem isNumberingOf {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    {marked : Fin n → Prop} {b : d.Vertex ≃ Fin n}
    (h : d.IsNumberingOf M marked b) :
    e.IsNumberingOf M marked (f.vertices.symm.trans b) := by
  constructor
  · intro a a'
    change e.cartan a a' = M (b (f.vertices.symm a)) (b (f.vertices.symm a'))
    calc
      e.cartan a a' = e.cartan (f.vertices (f.vertices.symm a))
          (f.vertices (f.vertices.symm a')) := by simp
      _ = d.cartan (f.vertices.symm a) (f.vertices.symm a') := f.cartan_eq _ _
      _ = M (b (f.vertices.symm a)) (b (f.vertices.symm a')) := h.1 _ _
  · intro a
    simpa using ((f.distinguished_iff (f.vertices.symm a)).symm.trans
      (h.2 (f.vertices.symm a)))

/-- Triviality is transferred for every element of the full Galois group. -/
theorem starIsTrivial (h : d.StarIsTrivial) : e.StarIsTrivial := by
  intro σ a
  obtain ⟨b, rfl⟩ := f.vertices.surjective a
  rw [← f.star_eq, h]

/-- Transport an exact two-element star image with the same displayed permutation. -/
theorem starImagePair {n : ℕ} {b : d.Vertex ≃ Fin n} {τ : Equiv.Perm (Fin n)}
    (h : d.StarImagePair b τ) :
    e.StarImagePair (f.vertices.symm.trans b) τ := by
  have hstar (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : e.Vertex) :
      f.vertices.symm (e.star σ a) = d.star σ (f.vertices.symm a) := by
    apply f.vertices.injective
    simpa using (f.star_eq σ (f.vertices.symm a)).symm
  refine ⟨h.1, ?_, ?_⟩
  · intro σ
    rcases h.2.1 σ with hσ | hσ
    · left
      intro a
      change b (f.vertices.symm (e.star σ a)) = b (f.vertices.symm a)
      rw [hstar]
      exact hσ _
    · right
      intro a
      change b (f.vertices.symm (e.star σ a)) = τ (b (f.vertices.symm a))
      rw [hstar]
      exact hσ _
  · obtain ⟨σ, hσ⟩ := h.2.2
    refine ⟨σ, ?_⟩
    intro a
    change b (f.vertices.symm (e.star σ a)) = τ (b (f.vertices.symm a))
    rw [hstar]
    exact hσ _

/-- The inner-A alternative preserves its degree, precise mark and trivial action. -/
theorem hasRankOneInnerAIndex {degree : ℕ} (h : d.HasRankOneInnerAIndex degree) :
    e.HasRankOneInnerAIndex degree := by
  obtain ⟨hdegree, ⟨b, hb⟩, hstar⟩ := h
  exact ⟨hdegree, ⟨f.vertices.symm.trans b, f.isNumberingOf hb⟩, f.starIsTrivial hstar⟩

/-- The outer-A alternative preserves its rank, endpoint marks and exact full image. -/
theorem hasRankOneOuterAIndex {n : ℕ} (h : d.HasRankOneOuterAIndex n) :
    e.HasRankOneOuterAIndex n := by
  obtain ⟨hn, b, hb, hstar⟩ := h
  exact ⟨hn, f.vertices.symm.trans b, f.isNumberingOf hb, f.starImagePair hstar⟩

/-- The C alternative preserves its rank, exact marked vertex and trivial action. -/
theorem hasRankOneCIndex {n : ℕ} (h : d.HasRankOneCIndex n) :
    e.HasRankOneCIndex n := by
  obtain ⟨hn, ⟨b, hb⟩, hstar⟩ := h
  exact ⟨hn, ⟨f.vertices.symm.trans b, f.isNumberingOf hb⟩, f.starIsTrivial hstar⟩

/-- The outer-D4 alternative preserves its central mark and exact full image. -/
theorem hasRankOneOuterD4Index (h : d.HasRankOneOuterD4Index) :
    e.HasRankOneOuterD4Index := by
  obtain ⟨b, hb, hstar⟩ := h
  exact ⟨f.vertices.symm.trans b, f.isNumberingOf hb, f.starImagePair hstar⟩

/-- The inner-D5 alternative preserves its exact mark and trivial full action. -/
theorem hasRankOneInnerD5Index (h : d.HasRankOneInnerD5Index) :
    e.HasRankOneInnerD5Index := by
  obtain ⟨⟨b, hb⟩, hstar⟩ := h
  exact ⟨⟨f.vertices.symm.trans b, f.isNumberingOf hb⟩, f.starIsTrivial hstar⟩

/-- The entire five-alternative conclusion transfers along an actual index comparison. -/
theorem rankOneAlternatives
    (h : (∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) :
    (∃ degree : ℕ, e.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, e.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, e.HasRankOneCIndex n) ∨
      e.HasRankOneOuterD4Index ∨ e.HasRankOneInnerD5Index := by
  rcases h with ⟨degree, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h
  · exact Or.inl ⟨degree, f.hasRankOneInnerAIndex h⟩
  · exact Or.inr (Or.inl ⟨n, f.hasRankOneOuterAIndex h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, f.hasRankOneCIndex h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (f.hasRankOneOuterD4Index h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (f.hasRankOneInnerD5Index h))))

end TitsIndexEquiv

end Langlands.GroupScheme
