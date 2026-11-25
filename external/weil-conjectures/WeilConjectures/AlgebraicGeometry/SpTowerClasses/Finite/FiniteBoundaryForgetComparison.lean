/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteBoundaryUnderlyingEvaluation
/-! # Forgetting scalar restriction commutes with finite evaluation -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Identity transports intertwine heterogeneous additive maps.
Source: equality elimination (blueprint: def-sfb-finite-forget-comparison). -/
theorem finiteBoundary_transport_addHom {A B A' B' : AddCommGrpCat.{u + 1}}
    (eA : A = A') (eB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f.hom g.hom) :
    f ≫ eqToHom eB = eqToHom eA ≫ g := by
  subst A'
  subst B'
  have h' := eq_of_heq h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact AddCommGrpCat.hom_ext h'

/-- The recorded forgetting agrees with additive pushforward at each finite level.
Source: the section, restriction and morphism equations of Forget.
(blueprint: def-sfb-finite-forget-comparison). -/
def forgetUnderlyingEvaluationIso (T : Scheme.{u})
    (R : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T R) (n : ℕ) :
    F.F ⋙ abEvaluation T n ≅
      SheafOfModules.toSheaf (SemilinearSections.ring
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op))) ⋙
        (Prod.sectR n T.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (Scheme.ProEt.topology T) (coefficientSequenceTopology (Scheme.ProEt.topology T)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let G : T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
      (Prod.sectR n T.ProEt).op ⋙ M.val.presheaf
    let e₀ : ((F.F.obj M).obj (op n)).obj ≅ G := by
      refine NatIso.ofComponents (fun U ↦ eqToIso (F.sections M n U)) ?_
      intro U V f
      exact finiteBoundary_transport_addHom (F.sections M n U) (F.sections M n V)
        _ (G.map f) (F.restrictions M n f)
    exact ObjectProperty.isoMk _ e₀
  · intro M N f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact finiteBoundary_transport_addHom (F.sections M n U) (F.sections N n U)
      _ _ (F.morphisms f n U)

/-- Restriction of module scalars retains the underlying additive evaluation.
Source: the section equations of Forget and additive restriction and evaluation.
(blueprint: def-sfb-finite-forget-comparison). -/
def forgetScalarEvaluationIso (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (F : Forget T R) (n : ℕ) :
    SemilinearSections.res φ ⋙ F.F ⋙ abEvaluation T n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op) n ⋙
        SheafOfModules.toSheaf (SemilinearSections.ring (Scheme.ProEt.topology T)
          (A.obj (op n))) :=
  Functor.isoWhiskerLeft (SemilinearSections.res φ) (forgetUnderlyingEvaluationIso T R F n) ≪≫
    Functor.isoWhiskerRight (SemilinearSections.restrictionToSheafIso
      (coefficientSequenceTopology (Scheme.ProEt.topology T)) φ)
      ((Prod.sectR n T.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.ProEt.topology T) (coefficientSequenceTopology (Scheme.ProEt.topology T))) ≪≫
    (SemilinearSections.evaluationToSheafIso (Scheme.ProEt.topology T)
      (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op) n).symm

/-- The actual underlying additive sheaves are unchanged by restricting scalars.
Source: classes proof (2), the section and morphism equations of Forget.
(blueprint: def-sfb-finite-forget-comparison). -/
def finiteScalarForgetIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :
    SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T) ⋙
        c.reduction.forget.F ⋙ abEvaluation T n ≅
      SpTowerShriek.ev l E T n ⋙ finiteForget l E T n :=
  forgetScalarEvaluationIso T (Rrings l T) (Arings l E T) (coefficientSystemMap l E T)
    c.reduction.forget n

/-- An identity transport sends a section to its heterogeneous representative.
Source: equality elimination (blueprint: def-sfb-finite-forget-comparison). -/
theorem finiteBoundary_transport_element {A B : AddCommGrpCat.{u + 1}} (e : A = B)
    (x : A) (y : B) (h : HEq x y) : (eqToHom e) x = y := by
  subst B
  exact eq_of_heq h

/-- The forgetting comparison sends a forgotten section to the same actual section.
Source: the definition of finiteScalarForgetIso
(blueprint: def-sfb-finite-forget-comparison). -/
theorem finiteScalarForgetIso_section (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (n : ℕ)
    (M : Systems T (Arings l E T)) (U : T.ProEtᵒᵖ)
    (x' : ((c.reduction.forget.F.obj
      ((SemilinearSections.res (coefficientSystemMap l E T)).obj M)).obj (op n)).obj.obj U)
    (x : M.val.obj (op (n, U.unop))) (hx : HEq x' x) :
    ((finiteScalarForgetIso l E c n).hom.app M).hom.app U x' = x := by
  change (eqToHom (c.reduction.forget.sections
    ((SemilinearSections.res (coefficientSystemMap l E T)).obj M) n U)) x' = x
  exact finiteBoundary_transport_element (c.reduction.forget.sections
    ((SemilinearSections.res (coefficientSystemMap l E T)).obj M) n U) x' x hx

/-- Recorded forgetting takes a module morphism to its actual map on sections.
Source: the morphism field of Forget, by heterogeneous equality elimination.
(blueprint: def-sfb-finite-forget-comparison). -/
theorem finiteBoundary_forgetMapSection (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {M N : Systems T B} (a : M ⟶ N)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop)))
    (x' : ((F.F.obj M).obj (op n)).obj.obj U) (hx : HEq x' x) :
    HEq (((F.F.map a).app (op n)).hom.app U x')
      (a.val.app (op (n, U.unop)) x) := by
  have happ {A B A' B' : AddCommGrpCat.{u + 1}}
      (hA : A = A') (hB : B = B') {f : A →+ B} {g : A' →+ B'}
      (hf : HEq f g) {x : A} {y : A'} (hx : HEq x y) :
      HEq (f x) (g y) := by
    cases hA
    cases hB
    exact heq_of_eq (congrArg (fun k : A →+ B ↦ k x) (eq_of_heq hf) |>.trans
      (congrArg g (eq_of_heq hx)))
  exact happ (F.sections M n U) (F.sections N n U) (F.morphisms a n U) hx

/-- Identity transport retains a section heterogeneously.
Source: equality elimination (blueprint: def-sfb-finite-forget-comparison). -/
theorem finiteBoundary_cast_heq {A B : AddCommGrpCat.{u + 1}} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst B
  rfl
end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
