import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.MatchingAlgebra

/-! # Matching families of restricted local pieces over full domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)}

namespace LocalAlgebras

variable (F : LocalAlgebras c)

/-- Restrictions between closed-quotient base changes compose. -/
theorem restrict_comp (i : Fin c.size) {E D G : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDG : D.locus ⊆ G.locus) (hGi : G.locus ⊆ (c.obj i).locus) :
    (F.restrict i hED (hDG.trans hGi)).comp (F.restrict i hDG hGi) =
      F.restrict i (hED.trans hDG) hGi := by
  apply AffinoidPushout.hom_ext (F.map i) (restriction hGi)
  · change ((F.restrict i hED (hDG.trans hGi)).comp (F.restrict i hDG hGi)).comp
        (F.localMap i G hGi) = (F.restrict i (hED.trans hDG) hGi).comp (F.localMap i G hGi)
    rw [BoundedAlgHom.comp_assoc, F.restrict_localMap, F.restrict_localMap,
      F.restrict_localMap]
  · change ((F.restrict i hED (hDG.trans hGi)).comp (F.restrict i hDG hGi)).comp
        (F.baseMap i G hGi) = (F.restrict i (hED.trans hDG) hGi).comp (F.baseMap i G hGi)
    rw [BoundedAlgHom.comp_assoc, F.restrict_baseMap, ← BoundedAlgHom.comp_assoc,
      F.restrict_baseMap, BoundedAlgHom.comp_assoc, restriction_comp, F.restrict_baseMap]

theorem restrict_restrict (i : Fin c.size) {E D G : Domain K R}
    (hED : E.locus ⊆ D.locus) (hDG : D.locus ⊆ G.locus) (hGi : G.locus ⊆ (c.obj i).locus)
    (x : F.baseChange i G hGi) :
    F.restrict i hED (hDG.trans hGi) (F.restrict i hDG hGi x) =
      F.restrict i (hED.trans hDG) hGi x :=
  congrArg (fun q : BoundedAlgHom K (F.baseChange i G hGi)
    (F.baseChange i E ((hED.trans hDG).trans hGi)) => q x) (F.restrict_comp i hED hDG hGi)

end LocalAlgebras

namespace PairTransitions

variable {F : LocalAlgebras c} (t : PairTransitions F)

/-- The local leg of a restricted transition, with an explicit overlap containment. -/
theorem transition_localMap' (i j : Fin c.size) (E : Domain K R)
    (hi : E.locus ⊆ (c.obj i).locus) (hj : E.locus ⊆ (c.obj j).locus)
    (hEo : E.locus ⊆ (F.overlap i j).locus) :
    (t.transition i j E hi hj).comp (F.localMap i E hi) =
      (F.restrict j hEo (F.overlapRight i j)).comp ((t.equiv i j).toBoundedAlgHom.comp
        (F.localMap i (F.overlap i j) (F.overlapLeft i j))) :=
  (t.transition_localMap i j E hi hj).trans (BoundedAlgHom.comp_assoc _ _ _)

/-- Transitions commute with restriction to smaller full domains. -/
theorem restrict_transition (i j : Fin c.size) {E D : Domain K R} (hED : E.locus ⊆ D.locus)
    (hDi : D.locus ⊆ (c.obj i).locus) (hDj : D.locus ⊆ (c.obj j).locus) :
    (F.restrict j hED hDj).comp (t.transition i j D hDi hDj) =
      (t.transition i j E (Set.Subset.trans hED hDi) (Set.Subset.trans hED hDj)).comp
        (F.restrict i hED hDi) := by
  have hDo : D.locus ⊆ (F.overlap i j).locus := fun _ hx => ⟨hDi hx, hDj hx⟩
  apply AffinoidPushout.hom_ext (F.map i) (restriction hDi)
  · change ((F.restrict j hED hDj).comp (t.transition i j D hDi hDj)).comp
        (F.localMap i D hDi) = ((t.transition i j E _ _).comp
          (F.restrict i hED hDi)).comp (F.localMap i D hDi)
    rw [BoundedAlgHom.comp_assoc, t.transition_localMap' i j D hDi hDj hDo,
      BoundedAlgHom.comp_assoc (t.transition i j E _ _), F.restrict_localMap,
      t.transition_localMap' i j E _ _ (Set.Subset.trans hED hDo), ← BoundedAlgHom.comp_assoc,
      F.restrict_comp]
  · change ((F.restrict j hED hDj).comp (t.transition i j D hDi hDj)).comp
        (F.baseMap i D hDi) = ((t.transition i j E _ _).comp
          (F.restrict i hED hDi)).comp (F.baseMap i D hDi)
    rw [BoundedAlgHom.comp_assoc, t.transition_baseMap, F.restrict_baseMap,
      BoundedAlgHom.comp_assoc, F.restrict_baseMap, ← BoundedAlgHom.comp_assoc,
      t.transition_baseMap]

theorem inter_subset_member (V : Domain K R) (i : Fin c.size) :
    (V.inter (c.obj i)).locus ⊆ (c.obj i).locus := Set.inter_subset_right

/-- The `i`-th local algebra changed to the intersection of `V` with the `i`-th
cover member. -/
abbrev piece (_t : PairTransitions F) (V : Domain K R) (i : Fin c.size) :
    PresentedAffinoidAlgebra K :=
  F.baseChange i (V.inter (c.obj i)) (inter_subset_member V i)

theorem inter_subset_inter {V' V : Domain K R} (h : V'.locus ⊆ V.locus) (i : Fin c.size) :
    (V'.inter (c.obj i)).locus ⊆ (V.inter (c.obj i)).locus :=
  fun _ hx => ⟨h hx.1, hx.2⟩

/-- Restriction of pieces along a containment of full domains. -/
def pieceRestrict {V' V : Domain K R} (h : V'.locus ⊆ V.locus) (i : Fin c.size) :
    BoundedAlgHom K (t.piece V i) (t.piece V' i) :=
  F.restrict i (inter_subset_inter h i) (inter_subset_member V i)

/-- A family of pieces over `V` matches if, for every full domain `E` inside
`V ∩ cᵢ` and `V ∩ cⱼ`, the transition carries the restriction of the `i`-th
member to the restriction of the `j`-th member. -/
def IsMatching (V : Domain K R) (m : ∀ i, t.piece V i) : Prop :=
  ∀ (i j : Fin c.size) (E : Domain K R) (hi : E.locus ⊆ (V.inter (c.obj i)).locus)
    (hj : E.locus ⊆ (V.inter (c.obj j)).locus),
    t.transition i j E (Set.Subset.trans hi (inter_subset_member V i))
        (Set.Subset.trans hj (inter_subset_member V j))
        (F.restrict i hi (inter_subset_member V i) (m i)) =
      F.restrict j hj (inter_subset_member V j) (m j)

/-- The algebra of matching families of pieces over a full domain. -/
def pieceMatching (V : Domain K R) : Subalgebra K (∀ i, t.piece V i) where
  carrier := {m | t.IsMatching V m}
  zero_mem' := by intro i j E hi hj; simp only [Pi.zero_apply, map_zero]
  one_mem' := by intro i j E hi hj; simp only [Pi.one_apply, map_one]
  add_mem' := by
    intro m m' hm hm' i j E hi hj
    simp only [Pi.add_apply, map_add]
    rw [hm i j E hi hj, hm' i j E hi hj]
  mul_mem' := by
    intro m m' hm hm' i j E hi hj
    simp only [Pi.mul_apply, map_mul]
    rw [hm i j E hi hj, hm' i j E hi hj]
  algebraMap_mem' := by
    intro a i j E hi hj
    exact ((congrArg (t.transition i j E _ _) ((F.restrict i hi _).toAlgHom.commutes a)).trans
      ((t.transition i j E _ _).toAlgHom.commutes a)).trans
        ((F.restrict j hj _).toAlgHom.commutes a).symm

/-- Restriction of matching families along a containment of full domains. -/
def matchingRestrict {V' V : Domain K R} (h : V'.locus ⊆ V.locus) :
    t.pieceMatching V →ₐ[K] t.pieceMatching V' :=
  (AlgHom.pi fun i => (t.pieceRestrict h i).toAlgHom.comp
      ((Pi.evalAlgHom K (fun i => t.piece V i) i).comp (t.pieceMatching V).val)).codRestrict
    (t.pieceMatching V') (fun m i j E hi hj =>
      (congrArg (t.transition i j E _ _) (F.restrict_restrict i hi (inter_subset_inter h i)
        (inter_subset_member V i) (m.val i))).trans
      ((m.property i j E (Set.Subset.trans hi (inter_subset_inter h i))
        (Set.Subset.trans hj (inter_subset_inter h j))).trans
      (F.restrict_restrict j hj (inter_subset_inter h j) (inter_subset_member V j)
        (m.val j)).symm))

@[simp] theorem matchingRestrict_apply {V' V : Domain K R} (h : V'.locus ⊆ V.locus)
    (m : t.pieceMatching V) (i : Fin c.size) :
    (t.matchingRestrict h m).val i = t.pieceRestrict h i (m.val i) := rfl

/-- The structural algebra map from the domain algebra to matching families. -/
def matchingStructure (V : Domain K R) : V.algebra →ₐ[K] t.pieceMatching V :=
  (AlgHom.pi fun i => (F.baseMap i (V.inter (c.obj i)) (inter_subset_member V i)).toAlgHom.comp
      (restriction (Set.inter_subset_left :
        (V.inter (c.obj i)).locus ⊆ V.locus)).toAlgHom).codRestrict
    (t.pieceMatching V) (fun a i j E hi hj => by
      have key : ∀ k (hk : E.locus ⊆ (V.inter (c.obj k)).locus),
          F.restrict k hk (inter_subset_member V k)
              (F.baseMap k (V.inter (c.obj k)) (inter_subset_member V k)
                (restriction (Set.inter_subset_left :
                  (V.inter (c.obj k)).locus ⊆ V.locus) a)) =
            F.baseMap k E (Set.Subset.trans hk (inter_subset_member V k))
              (restriction (Set.Subset.trans hk Set.inter_subset_left) a) := by
        intro k hk
        have h1 := congrArg (fun q : BoundedAlgHom K (V.inter (c.obj k)).algebra
          (F.baseChange k E (Set.Subset.trans hk (inter_subset_member V k))) =>
            q (restriction (Set.inter_subset_left :
              (V.inter (c.obj k)).locus ⊆ V.locus) a))
          (F.restrict_baseMap k hk (inter_subset_member V k))
        have h2 := congrArg (fun q : BoundedAlgHom K V.algebra E.algebra => q a)
          (restriction_comp hk (Set.inter_subset_left :
            (V.inter (c.obj k)).locus ⊆ V.locus))
        exact h1.trans (congrArg _ h2)
      exact (congrArg (t.transition i j E _ _) (key i hi)).trans
        ((congrArg (fun q : BoundedAlgHom K E.algebra
          (F.baseChange j E (Set.Subset.trans hj (inter_subset_member V j))) =>
            q (restriction (Set.Subset.trans hi Set.inter_subset_left) a))
          (t.transition_baseMap i j E _ _)).trans (key j hj).symm))

@[simp] theorem matchingStructure_apply (V : Domain K R) (a : V.algebra) (i : Fin c.size) :
    (t.matchingStructure V a).val i =
      F.baseMap i (V.inter (c.obj i)) (inter_subset_member V i)
        (restriction (Set.inter_subset_left : (V.inter (c.obj i)).locus ⊆ V.locus) a) := rfl

/-- A finite family of matching families generates over the domain algebra. -/
def Generates (V : Domain K R) {n : ℕ} (s : Fin n → t.pieceMatching V) : Prop :=
  ∀ m : t.pieceMatching V, ∃ a : Fin n → V.algebra, ∑ k, t.matchingStructure V (a k) * s k = m

/-- The components of a finite family of matching families generate every piece
`piece V i` as a module over the algebra of `V ∩ cᵢ`, acting through the pushout
leg `F.baseMap i`. -/
def PiecesGenerate (V : Domain K R) {n : ℕ} (s : Fin n → t.pieceMatching V) : Prop :=
  ∀ (i : Fin c.size) (p : t.piece V i), ∃ a : Fin n → (V.inter (c.obj i)).algebra,
    ∑ k, F.baseMap i (V.inter (c.obj i)) (inter_subset_member V i) (a k) * (s k).val i = p

end PairTransitions

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
