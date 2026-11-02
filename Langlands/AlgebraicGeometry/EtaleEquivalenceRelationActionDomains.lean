import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLawTransport

/-! # Cartesian domains for prospective actions

The arrow and composable-input domains are base changes over their outer
targets when both the relation morphism and object square are cartesian.
No action map or action law is needed.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

variable {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
  {P Q : Scheme.{u}} {p : P ⟶ E.U} {q : Q ⟶ F.U}
  {k : P ⟶ Q} (hp : IsPullback k p q f)

/-- The action-arrow domain is also a pullback over the original arrow scheme. -/
lemma isPullback_arrowMap_fst :
    IsPullback (arrowMap h p q k hp.w.symm) (pullback.fst E.s p)
      (pullback.fst F.s q) g := by
  refine IsPullback.mk' (arrowMap_fst h p q k hp.w.symm) ?_ ?_
  · intro T x y hx hr
    apply pullback.hom_ext
    · exact hr
    · apply hp.hom_ext
      · simpa only [Category.assoc, arrowMap_snd] using
          congrArg (· ≫ pullback.snd F.s q) hx
      · simpa only [Category.assoc, ← pullback.condition] using
          congrArg (· ≫ E.s) hr
  · intro T z r hz
    have hv : (z ≫ pullback.snd F.s q) ≫ q = (r ≫ E.s) ≫ f := by
      calc
        (z ≫ pullback.snd F.s q) ≫ q =
            (z ≫ pullback.fst F.s q) ≫ F.s := by
          rw [Category.assoc, ← pullback.condition, ← Category.assoc]
        _ = (r ≫ g) ≫ F.s := by rw [hz]
        _ = (r ≫ E.s) ≫ f := by rw [Category.assoc, h.2.w, ← Category.assoc]
    let v := hp.lift (z ≫ pullback.snd F.s q) (r ≫ E.s) hv
    refine ⟨pullback.lift r v (hp.lift_snd _ _ _).symm, ?_,
      pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, arrowMap_fst, pullback.lift_fst_assoc]
      exact hz.symm
    · simp only [Category.assoc, arrowMap_snd, pullback.lift_snd_assoc]
      exact hp.lift_fst _ _ _

/-- The prospective action domain is a base change over the arrow target. -/
lemma isPullback_arrowMap_target :
    IsPullback (arrowMap h p q k hp.w.symm) (pullback.fst E.s p ≫ E.t)
      (pullback.fst F.s q ≫ F.t) f :=
  (isPullback_arrowMap_fst h hp).paste_vert h.isPullback_t

/-- Identify the action-arrow domain with the base change over its target. -/
noncomputable def arrowDomainTargetIso :
    pullback E.s p ≅ pullback (pullback.fst F.s q ≫ F.t) f :=
  (isPullback_arrowMap_target h hp).isoPullback

@[reassoc (attr := simp)]
lemma arrowDomainTargetIso_hom_fst :
    (arrowDomainTargetIso h hp).hom ≫ pullback.fst _ _ =
      arrowMap h p q k hp.w.symm :=
  (isPullback_arrowMap_target h hp).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma arrowDomainTargetIso_hom_snd :
    (arrowDomainTargetIso h hp).hom ≫ pullback.snd _ _ =
      pullback.fst E.s p ≫ E.t :=
  (isPullback_arrowMap_target h hp).isoPullback_hom_snd

/-- The map on composable inputs is the iterated map on arrow domains. -/
lemma composableMap_eq_arrowMap :
    composableMap h p q k hp.w.symm =
      arrowMap h (pullback.fst E.s p ≫ E.t) (pullback.fst F.s q ≫ F.t)
        (arrowMap h p q k hp.w.symm) (isPullback_arrowMap_target h hp).w.symm := by
  apply pullback.hom_ext
  · exact (composableMap_outerArrow h p q k hp.w.symm).trans
      (arrowMap_fst _ _ _ _ _).symm
  · apply pullback.hom_ext
    · simp only [Category.assoc, arrowMap_snd_assoc, arrowMap_fst]
      exact composableMap_innerArrow h p q k hp.w.symm
    · simp only [Category.assoc, arrowMap_snd]
      exact composableMap_sourcePoint h p q k hp.w.symm

/-- Composable inputs are cartesian over the outer original arrow. -/
lemma isPullback_composableMap_outerArrow :
    IsPullback (composableMap h p q k hp.w.symm) (outerArrow E p)
      (outerArrow F q) g := by
  rw [composableMap_eq_arrowMap h hp]
  exact isPullback_arrowMap_fst h (isPullback_arrowMap_target h hp)

/-- Composable inputs are cartesian over the outer arrow target. -/
lemma isPullback_composableMap_target :
    IsPullback (composableMap h p q k hp.w.symm) (outerArrow E p ≫ E.t)
      (outerArrow F q ≫ F.t) f :=
  (isPullback_composableMap_outerArrow h hp).paste_vert h.isPullback_t

/-- Identify the composable-input domain with its target base change. -/
noncomputable def composableDomainTargetIso :
    composable E p ≅ pullback (outerArrow F q ≫ F.t) f :=
  (isPullback_composableMap_target h hp).isoPullback

@[reassoc (attr := simp)]
lemma composableDomainTargetIso_hom_fst :
    (composableDomainTargetIso h hp).hom ≫ pullback.fst _ _ =
      composableMap h p q k hp.w.symm :=
  (isPullback_composableMap_target h hp).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma composableDomainTargetIso_hom_snd :
    (composableDomainTargetIso h hp).hom ≫ pullback.snd _ _ =
      outerArrow E p ≫ E.t :=
  (isPullback_composableMap_target h hp).isoPullback_hom_snd

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
