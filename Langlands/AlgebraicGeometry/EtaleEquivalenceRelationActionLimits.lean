import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionDomains

/-! # Target base change limits for action descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace TargetLimit

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {S T : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (q : T ⟶ S)

/-- The levelwise base change along a fixed target map. -/
noncomputable def diagram : I ⥤ Scheme.{u} :=
  Over.lift D t ⋙ Over.pullback q ⋙ Over.forget T

/-- Projection of the base changed diagram to its fixed factor. -/
noncomputable def comparison : diagram D t q ⟶ (Functor.const I).obj T where
  app i := pullback.snd (t.app i) q
  naturality _ _ a := by
    dsimp [diagram, Over.pullback, Over.lift]
    simp

/-- Projection of the base changed diagram to the varying factor. -/
noncomputable def projection : diagram D t q ⟶ D where
  app i := pullback.fst (t.app i) q
  naturality _ _ a := by
    dsimp [diagram, Over.pullback, Over.lift]
    simp

variable (c : Cone D) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

/-- Base change of a supplied cone, retaining an explicit structural map. -/
noncomputable def cone : Cone (diagram D t q) :=
  (Over.pullback q ⋙ Over.forget T).mapCone (Over.liftCone D t c p hp)

attribute [local instance] IsCofiltered.isConnected

/-- A cofiltered limit cone remains limiting after the target base change. -/
noncomputable def isLimitCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (cone D t q c p hp) :=
  isLimitOfPreserves (Over.pullback q ⋙ Over.forget T)
    (Over.isLimitLiftCone D t c p hp hc)

variable {X : Scheme.{u}} {l : X ⟶ c.pt} {k : X ⟶ T}
  (h : IsPullback l k p q)

/-- Replace the canonical base change by any supplied pullback square. -/
noncomputable def coneOfPullback : Cone (diagram D t q) :=
  (cone D t q c p hp).extend h.isoPullback.hom

@[reassoc (attr := simp)]
lemma coneOfPullback_π_fst (i : I) :
    (coneOfPullback D t q c p hp h).π.app i ≫ pullback.fst (t.app i) q =
      l ≫ c.π.app i := by
  dsimp [coneOfPullback, cone, diagram, Cone.extend, Functor.mapCone,
    Over.liftCone, Over.pullback]
  simp [Category.assoc]

@[reassoc (attr := simp)]
lemma coneOfPullback_π_snd (i : I) :
    (coneOfPullback D t q c p hp h).π.app i ≫ pullback.snd (t.app i) q = k := by
  dsimp [coneOfPullback, cone, diagram, Cone.extend, Functor.mapCone,
    Over.liftCone, Over.pullback]
  simp [Category.assoc]

/-- The cone on a supplied pullback is limiting. -/
noncomputable def isLimitConeOfPullback [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (coneOfPullback D t q c p hp h) :=
  IsLimit.extendIso (s := cone D t q c p hp) h.isoPullback.hom
    (isLimitCone D t q c p hp hc)

instance [IsAffine S] [IsAffine T] [∀ i, IsAffine (D.obj i)] (i : I) :
    IsAffine ((diagram D t q).obj i) := by
  change IsAffine (pullback (show D.obj i ⟶ S from t.app i) q)
  have : IsAffineHom q := inferInstance
  infer_instance

instance [IsAffine S] [IsAffine T] [∀ i, IsAffine (D.obj i)]
    {i j : I} (a : i ⟶ j) : IsAffineHom ((diagram D t q).map a) :=
  inferInstance

include hp in
/-- A map from the target base change of a limit to a finitely presented
object over the base factors at a level, with its base equation. -/
lemma exists_map_at_level [IsCofiltered I]
    [IsAffine S] [IsAffine T] [∀ i, IsAffine (D.obj i)]
    (hc : IsLimit c) {Q : Scheme.{u}} (r : Q ⟶ S)
    [LocallyOfFinitePresentation r]
    (a : X ⟶ Q) (ha : a ≫ r = k ≫ q) :
    ∃ (i : I) (b : (diagram D t q).obj i ⟶ Q),
      (coneOfPullback D t q c p hp h).π.app i ≫ b = a ∧
      b ≫ r = pullback.snd (t.app i) q ≫ q := by
  let v : diagram D t q ⟶ (Functor.const I).obj S :=
    comparison D t q ≫ (Functor.const I).map q
  exact Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (diagram D t q) v r (coneOfPullback D t q c p hp h)
    (isLimitConeOfPullback D t q c p hp h hc) a (by
      ext i
      simp only [v, NatTrans.comp_app, Functor.const_map_app,
        comparison, coneOfPullback_π_snd_assoc]
      exact ha.symm)

end TargetLimit

section ActionDomain

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u})
  {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
  {P Q : Scheme.{u}} {p : P ⟶ E.U} {q : Q ⟶ F.U}
  {k : P ⟶ Q} (hp : IsPullback k p q f)
  (t : D ⟶ (Functor.const I).obj F.U)
  (v : (Functor.const I).obj E.U ⟶ D)
  (hv : ∀ i, v.app i ≫ t.app i = f)

/-- The actual action-input domain is the point of the target base change cone. -/
noncomputable def arrowCone :
    Cone (TargetLimit.diagram D t (pullback.fst F.s q ≫ F.t)) :=
  TargetLimit.coneOfPullback D t (pullback.fst F.s q ≫ F.t)
    ⟨E.U, v⟩ f hv (isPullback_arrowMap_target h hp).flip

@[reassoc (attr := simp)]
lemma arrowCone_π_fst (i : I) :
    (arrowCone D h hp t v hv).π.app i ≫ pullback.fst (t.app i) _ =
      (pullback.fst E.s p ≫ E.t) ≫ v.app i :=
  TargetLimit.coneOfPullback_π_fst _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma arrowCone_π_snd (i : I) :
    (arrowCone D h hp t v hv).π.app i ≫ pullback.snd (t.app i) _ =
      arrowMap h p q k hp.w.symm :=
  TargetLimit.coneOfPullback_π_snd _ _ _ _ _ _ _ _

/-- An object limit gives the actual action-input domain as a limit. -/
noncomputable def isLimitArrowCone [IsCofiltered I]
    (hc : IsLimit (⟨E.U, v⟩ : Cone D)) :
    IsLimit (arrowCone D h hp t v hv) :=
  TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _ hc

include hv in
/-- The action map, followed by the fixed object comparison, factors at a level
of the target base change diagram. Its structural equation is retained. -/
lemma exists_target_factor_at_level [IsCofiltered I]
    [IsAffine F.U] [IsAffine (pullback F.s q)] [∀ i, IsAffine (D.obj i)]
    [LocallyOfFinitePresentation q]
    (hc : IsLimit (⟨E.U, v⟩ : Cone D)) (A : Action E p) :
    ∃ (i : I)
      (b : (TargetLimit.diagram D t (pullback.fst F.s q ≫ F.t)).obj i ⟶ Q),
      (arrowCone D h hp t v hv).π.app i ≫ b = A.map ≫ k ∧
      b ≫ q = pullback.snd (t.app i) (pullback.fst F.s q ≫ F.t) ≫
        (pullback.fst F.s q ≫ F.t) := by
  apply TargetLimit.exists_map_at_level D t (pullback.fst F.s q ≫ F.t)
    ⟨E.U, v⟩ f hv (isPullback_arrowMap_target h hp).flip hc q (A.map ≫ k)
  calc
    (A.map ≫ k) ≫ q = (A.map ≫ p) ≫ f := by
      rw [Category.assoc, hp.w, ← Category.assoc]
    _ = (pullback.fst E.s p ≫ E.t) ≫ f := by rw [A.over]
    _ = arrowMap h p q k hp.w.symm ≫ (pullback.fst F.s q ≫ F.t) := by
      rw [← Category.assoc, arrowMap_fst, Category.assoc, ← h.1,
        ← Category.assoc]

end ActionDomain

section FactorLift

variable {E F : EtaleEquivalenceRelation.{u}}
  {f : E.U ⟶ F.U} {g : E.R ⟶ F.R} (h : IsCartesianHom E F f g)
  {P Q : Scheme.{u}} {p : P ⟶ E.U} {q : Q ⟶ F.U}
  {k : P ⟶ Q} (hp : IsPullback k p q f)
  (b : pullback f (pullback.fst F.s q ≫ F.t) ⟶ Q)
  (hb : b ≫ q = pullback.snd f (pullback.fst F.s q ≫ F.t) ≫
    (pullback.fst F.s q ≫ F.t))

/-- Lift a target-base-change factor to a prospective action map at that level. -/
noncomputable def targetFactorMap : pullback E.s p ⟶ P :=
  hp.lift ((isPullback_arrowMap_target h hp).flip.isoPullback.hom ≫ b)
    (pullback.fst E.s p ≫ E.t) (by
      rw [Category.assoc, hb, ← Category.assoc,
        (isPullback_arrowMap_target h hp).flip.isoPullback_hom_snd]
      exact (isPullback_arrowMap_target h hp).w)

@[reassoc (attr := simp)]
lemma targetFactorMap_comparison :
    targetFactorMap h hp b hb ≫ k =
      (isPullback_arrowMap_target h hp).flip.isoPullback.hom ≫ b :=
  hp.lift_fst _ _ _

@[reassoc]
lemma targetFactorMap_over :
    targetFactorMap h hp b hb ≫ p = pullback.fst E.s p ≫ E.t :=
  hp.lift_snd _ _ _

end FactorLift

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action
