import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAction

/-! # Cartesian morphisms of action relations

An equivariant map of actions over a cartesian relation morphism induces a
cartesian morphism of the associated equivalence relations.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

variable {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
  {P Q : Scheme.{u}} (p : P ⟶ E.U) (q : Q ⟶ F.U)
  (k : P ⟶ Q) (w : p ≫ f = k ≫ q)

/-- The map of action-arrow schemes induced by commuting object maps. -/
noncomputable def arrowMap : pullback E.s p ⟶ pullback F.s q :=
  pullback.lift (pullback.fst E.s p ≫ g) (pullback.snd E.s p ≫ k)
    (by rw [Category.assoc, h.2.w, ← Category.assoc, pullback.condition,
      Category.assoc, w, ← Category.assoc])

@[reassoc (attr := simp)]
lemma arrowMap_fst :
    arrowMap h p q k w ≫ pullback.fst F.s q = pullback.fst E.s p ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma arrowMap_snd :
    arrowMap h p q k w ≫ pullback.snd F.s q = pullback.snd E.s p ≫ k :=
  pullback.lift_snd _ _ _

/-- Equivariance is a single equality of the target maps. -/
def IsEquivariant (A : Action E p) (B : Action F q) : Prop :=
  A.map ≫ k = arrowMap h p q k w ≫ B.map

/-- Arrow lifting in the original cartesian morphism proves cartesianness on
the action-arrow schemes. No pullback hypothesis on `k` is required. -/
lemma isPullback_arrowMap_snd :
    IsPullback (arrowMap h p q k w) (pullback.snd E.s p) (pullback.snd F.s q) k := by
  refine IsPullback.mk' (arrowMap_snd h p q k w) ?_ ?_
  · intro T x y hx hv
    apply pullback.hom_ext
    · apply h.2.hom_ext
      · simpa only [Category.assoc, arrowMap_fst] using
          congrArg (· ≫ pullback.fst F.s q) hx
      · simpa only [Category.assoc, pullback.condition] using congrArg (· ≫ p) hv
    · exact hv
  · intro T r₀ v hv
    have hr : (r₀ ≫ pullback.fst F.s q) ≫ F.s = (v ≫ p) ≫ f := by
      calc
        (r₀ ≫ pullback.fst F.s q) ≫ F.s =
            (r₀ ≫ pullback.snd F.s q) ≫ q := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
        _ = (v ≫ k) ≫ q := by rw [hv]
        _ = (v ≫ p) ≫ f := by rw [Category.assoc, ← w, ← Category.assoc]
    let r := h.2.lift (r₀ ≫ pullback.fst F.s q) (v ≫ p) hr
    have hrs : r ≫ E.s = v ≫ p := h.2.lift_snd _ _ _
    refine ⟨pullback.lift r v hrs, ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, arrowMap_fst, pullback.lift_fst_assoc]
      exact h.2.lift_fst _ _ _
    · simp only [Category.assoc, arrowMap_snd, pullback.lift_snd_assoc]
      exact hv.symm

/-- Equivariant object maps over a cartesian relation morphism give a
cartesian morphism of action relations. -/
lemma isCartesianHom_of_isEquivariant (A : Action E p) (B : Action F q)
    (hw : IsEquivariant h p q k w A B) :
    IsCartesianHom A.relation B.relation k (arrowMap h p q k w) :=
  ⟨hw.symm, isPullback_arrowMap_snd h p q k w⟩

/-- Equivariance on compatible scheme-valued arrows and points. -/
lemma act_naturality (A : Action E p) (B : Action F q)
    (hw : IsEquivariant h p q k w A B)
    {T : Scheme.{u}} (r : T ⟶ E.R) (v : T ⟶ P)
    (hrv : r ≫ E.s = v ≫ p) :
    A.act r v hrv ≫ k =
      B.act (r ≫ g) (v ≫ k)
        (by rw [Category.assoc, h.2.w, ← Category.assoc, hrv,
          Category.assoc, w, ← Category.assoc]) := by
  dsimp only [act]
  rw [Category.assoc, hw, ← Category.assoc]
  apply congrArg (· ≫ B.map)
  apply pullback.hom_ext <;>
    simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
