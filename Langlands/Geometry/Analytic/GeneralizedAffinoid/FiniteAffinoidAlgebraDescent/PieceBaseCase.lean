import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceGeneration

/-! # Matching families over full domains inside one cover member -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)}
  {F : LocalAlgebras c}

namespace PairTransitions

variable (t : PairTransitions F)

/-- Right-associated form of `restrict_transition`. -/
theorem restrict_transition_assoc {A' : Type*} [NormedCommRing A'] [Algebra K A']
    (i j : Fin c.size) {E D : Domain K R} (hED : E.locus ⊆ D.locus)
    (hDi : D.locus ⊆ (c.obj i).locus) (hDj : D.locus ⊆ (c.obj j).locus)
    (X : BoundedAlgHom K A' (F.baseChange i D hDi)) :
    (t.transition i j E (Set.Subset.trans hED hDi) (Set.Subset.trans hED hDj)).comp
        ((F.restrict i hED hDi).comp X) =
      (F.restrict j hED hDj).comp ((t.transition i j D hDi hDj).comp X) := by
  rw [← BoundedAlgHom.comp_assoc, ← t.restrict_transition, BoundedAlgHom.comp_assoc]

/-- The restricted transition from a member to itself is the identity, given the
identity condition on the original intersection. -/
theorem transition_self_of_identity {i : Fin c.size} (hid : (t.equiv i i).toBoundedAlgHom = BoundedAlgHom.id K _)
    (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) :
    t.transition i i E hi hi = BoundedAlgHom.id K _ := by
  have hEo : E.locus ⊆ (F.overlap i i).locus := fun _ hx => ⟨hi hx, hi hx⟩
  apply AffinoidPushout.hom_ext (F.map i) (restriction hi)
  · change (t.transition i i E hi hi).comp (F.localMap i E hi) =
      (BoundedAlgHom.id K _).comp (F.localMap i E hi)
    rw [t.transition_localMap' i i E hi hi hEo, hid, BoundedAlgHom.id_comp,
      F.restrict_localMap, BoundedAlgHom.id_comp]
  · change (t.transition i i E hi hi).comp (F.baseMap i E hi) =
      (BoundedAlgHom.id K _).comp (F.baseMap i E hi)
    rw [t.transition_baseMap, BoundedAlgHom.id_comp]

/-- The triple cocycle restricted to an arbitrary full domain. -/
theorem transition_cocycle_of_triple (i j k : Fin c.size)
    (hcoc : (t.transition j k (F.triple i j k) (F.tripleSecond i j k) (F.tripleThird i j k)).comp
        (t.transition i j (F.triple i j k) (F.tripleFirst i j k) (F.tripleSecond i j k)) =
      t.transition i k (F.triple i j k) (F.tripleFirst i j k) (F.tripleThird i j k))
    (E : Domain K R) (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus)
    (hk : E.locus ⊆ (c.obj k).locus) :
    (t.transition j k E hj hk).comp (t.transition i j E hi hj) = t.transition i k E hi hk := by
  have hT : E.locus ⊆ (F.triple i j k).locus := fun _ hx => ⟨⟨hi hx, hj hx⟩, hk hx⟩
  apply AffinoidPushout.hom_ext (F.map i) (restriction hi)
  · change ((t.transition j k E hj hk).comp (t.transition i j E hi hj)).comp
        (F.localMap i E hi) = (t.transition i k E hi hk).comp (F.localMap i E hi)
    rw [← F.restrict_localMap i hT (F.tripleFirst i j k), BoundedAlgHom.comp_assoc,
      t.restrict_transition_assoc i j hT (F.tripleFirst i j k) (F.tripleSecond i j k),
      t.restrict_transition_assoc j k hT (F.tripleSecond i j k) (F.tripleThird i j k),
      t.restrict_transition_assoc i k hT (F.tripleFirst i j k) (F.tripleThird i j k),
      ← BoundedAlgHom.comp_assoc (t.transition j k _ _ _), hcoc]
  · change ((t.transition j k E hj hk).comp (t.transition i j E hi hj)).comp
        (F.baseMap i E hi) = (t.transition i k E hi hk).comp (F.baseMap i E hi)
    rw [BoundedAlgHom.comp_assoc, t.transition_baseMap, t.transition_baseMap,
      t.transition_baseMap]

end PairTransitions

open PairTransitions

theorem inter_subset_of_subset {U : Domain K R} {i₀ : Fin c.size}
    (hU : U.locus ⊆ (c.obj i₀).locus) (j : Fin c.size) :
    (U.inter (c.obj j)).locus ⊆ (U.inter (c.obj i₀)).locus :=
  fun _ hx => ⟨hx.1, hU hx.1⟩

namespace DescentData

variable (d : DescentData F)

/-- The value at `y` of a restricted transition after restriction, for the
construction of matching families from one piece. -/
theorem restrict_transition_apply (i j : Fin c.size) {E D : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDi : D.locus ⊆ (c.obj i).locus)
    (hDj : D.locus ⊆ (c.obj j).locus) (y : F.baseChange i D hDi) :
    F.restrict j hED hDj (d.toPairTransitions.transition i j D hDi hDj y) =
      d.toPairTransitions.transition i j E (Set.Subset.trans hED hDi)
        (Set.Subset.trans hED hDj) (F.restrict i hED hDi y) :=
  congrArg (fun q : BoundedAlgHom K (F.baseChange i D hDi)
    (F.baseChange j E (Set.Subset.trans hED hDj)) => q y)
    (d.toPairTransitions.restrict_transition i j hED hDi hDj)

/-- A piece over a full domain inside the `i₀`-th member determines a matching
family by transitions; the triple cocycle gives the matching condition. -/
def ofPiece {U : Domain K R} (i₀ : Fin c.size) (hU : U.locus ⊆ (c.obj i₀).locus)
    (x : d.toPairTransitions.piece U i₀) : d.toPairTransitions.pieceMatching U :=
  ⟨fun j => d.toPairTransitions.transition i₀ j (U.inter (c.obj j))
      (Set.Subset.trans (inter_subset_of_subset hU j) (inter_subset_member U i₀))
      (inter_subset_member U j)
      (F.restrict i₀ (inter_subset_of_subset hU j) (inter_subset_member U i₀) x),
    fun j k E hj hk => by
      have hEi : E.locus ⊆ (c.obj i₀).locus := fun _ hx => hU (hj hx).1
      have key : ∀ (l : Fin c.size) (hl : E.locus ⊆ (U.inter (c.obj l)).locus),
          F.restrict l hl (inter_subset_member U l)
              (d.toPairTransitions.transition i₀ l (U.inter (c.obj l))
                (Set.Subset.trans (inter_subset_of_subset hU l) (inter_subset_member U i₀))
                (inter_subset_member U l)
                (F.restrict i₀ (inter_subset_of_subset hU l) (inter_subset_member U i₀) x)) =
            d.toPairTransitions.transition i₀ l E hEi
              (Set.Subset.trans hl (inter_subset_member U l))
              (F.restrict i₀ (Set.Subset.trans hl (inter_subset_of_subset hU l))
                (inter_subset_member U i₀) x) := fun l hl =>
        (d.restrict_transition_apply i₀ l hl _ _ _).trans
          (congrArg (d.toPairTransitions.transition i₀ l E _ _)
            (F.restrict_restrict i₀ hl (inter_subset_of_subset hU l)
              (inter_subset_member U i₀) x))
      have hcoc := congrArg (fun q : BoundedAlgHom K _ _ =>
          q (F.restrict i₀ (Set.Subset.trans hj (inter_subset_of_subset hU j))
            (inter_subset_member U i₀) x))
        (d.toPairTransitions.transition_cocycle_of_triple i₀ j k (d.cocycle i₀ j k) E hEi
          (Set.Subset.trans hj (inter_subset_member U j))
          (Set.Subset.trans hk (inter_subset_member U k)))
      exact (congrArg (d.toPairTransitions.transition j k E _ _) (key j hj)).trans
        (hcoc.trans (key k hk).symm)⟩

theorem ofPiece_apply {U : Domain K R} (i₀ : Fin c.size) (hU : U.locus ⊆ (c.obj i₀).locus)
    (x : d.toPairTransitions.piece U i₀) (j : Fin c.size) :
    (d.ofPiece i₀ hU x).val j = d.toPairTransitions.transition i₀ j (U.inter (c.obj j))
      (Set.Subset.trans (inter_subset_of_subset hU j) (inter_subset_member U i₀))
      (inter_subset_member U j)
      (F.restrict i₀ (inter_subset_of_subset hU j) (inter_subset_member U i₀) x) := rfl

end DescentData

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
