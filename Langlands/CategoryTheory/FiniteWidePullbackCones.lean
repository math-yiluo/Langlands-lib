import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Positive finite wide pullbacks from binary pullbacks -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Langlands.FiniteWidePullback

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- A one-arrow wide pullback is the source of that arrow. -/
def singletonCone {B : C} {Y : Fin 1 → C} (f : ∀ j, Y j ⟶ B) :
    WidePullbackCone f :=
  WidePullbackCone.mk (f 0)
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact 𝟙 _)
    (by
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp)

@[simp]
theorem singletonCone_π_zero {B : C} {Y : Fin 1 → C} (f : ∀ j, Y j ⟶ B) :
    (singletonCone f).π 0 = 𝟙 _ := rfl

@[simp]
theorem singletonCone_base {B : C} {Y : Fin 1 → C} (f : ∀ j, Y j ⟶ B) :
    (singletonCone f).base = f 0 := rfl

/-- The one-arrow construction has its universal property against all objects. -/
def singletonIsLimit {B : C} {Y : Fin 1 → C} (f : ∀ j, Y j ⟶ B) :
    IsLimit (singletonCone f) :=
  WidePullbackCone.IsLimit.mk _ (fun t => t.π 0)
    (fun t => t.condition 0)
    (by
      intro t j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change t.π 0 ≫ 𝟙 (Y 0) = t.π 0
      exact Category.comp_id _)
    (by
      intro t m _ hm
      have hm0 : m ≫ 𝟙 (Y 0) = t.π 0 := hm 0
      exact (Category.comp_id m).symm.trans hm0)

variable {n : ℕ} {B : C} {Y : Fin (n + 2) → C} (f : ∀ j, Y j ⟶ B)
  (s : WidePullbackCone (fun j : Fin (n + 1) => f j.succ))
  (p : PullbackCone (f 0) s.base)

/-- Adjoin the first arrow by pulling it back against the tail cone's base. -/
def consCone : WidePullbackCone f :=
  WidePullbackCone.mk (p.fst ≫ f 0)
    (fun j => Fin.cases p.fst (fun k => p.snd ≫ s.π k) j)
    (by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · change (p.snd ≫ s.π k) ≫ f k.succ = p.fst ≫ f 0
        rw [Category.assoc, s.condition, ← p.condition])

@[simp]
theorem consCone_base : (consCone f s p).base = p.fst ≫ f 0 := rfl

@[simp]
theorem consCone_π_zero : (consCone f s p).π 0 = p.fst := rfl

@[simp]
theorem consCone_π_succ (j : Fin (n + 1)) :
    (consCone f s p).π j.succ = p.snd ≫ s.π j := rfl

/-- The universal arrow to the tail of any cone on the full family. -/
def tailLift (hs : IsLimit s) (t : WidePullbackCone f) : t.pt ⟶ s.pt :=
  WidePullbackCone.IsLimit.lift hs t.base (fun j => t.π j.succ)
    (fun j => t.condition j.succ)

@[reassoc (attr := simp)]
theorem tailLift_base (hs : IsLimit s) (t : WidePullbackCone f) :
    tailLift f s hs t ≫ s.base = t.base :=
  WidePullbackCone.IsLimit.lift_base hs _ _ _

@[reassoc (attr := simp)]
theorem tailLift_π (hs : IsLimit s) (t : WidePullbackCone f) (j : Fin (n + 1)) :
    tailLift f s hs t ≫ s.π j = t.π j.succ :=
  WidePullbackCone.IsLimit.lift_π hs _ _ _ j

/-- The universal arrow to the cone obtained by adjoining the first arrow. -/
def consLift (hs : IsLimit s) (hp : IsLimit p) (t : WidePullbackCone f) :
    t.pt ⟶ p.pt :=
  (IsPullback.of_isLimit hp).lift (t.π 0) (tailLift f s hs t)
    (by rw [tailLift_base, t.condition])

@[reassoc (attr := simp)]
theorem consLift_fst (hs : IsLimit s) (hp : IsLimit p) (t : WidePullbackCone f) :
    consLift f s p hs hp t ≫ p.fst = t.π 0 :=
  (IsPullback.of_isLimit hp).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem consLift_snd (hs : IsLimit s) (hp : IsLimit p) (t : WidePullbackCone f) :
    consLift f s p hs hp t ≫ p.snd = tailLift f s hs t :=
  (IsPullback.of_isLimit hp).lift_snd _ _ _

/-- A limiting tail and a limiting binary pullback give a limiting full cone. -/
def consIsLimit (hs : IsLimit s) (hp : IsLimit p) : IsLimit (consCone f s p) :=
  WidePullbackCone.IsLimit.mk _ (consLift f s p hs hp)
    (fun t => by
      change consLift f s p hs hp t ≫ (p.fst ≫ f 0) = t.base
      rw [← Category.assoc, consLift_fst, t.condition])
    (by
      intro t j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact consLift_fst f s p hs hp t
      · change consLift f s p hs hp t ≫ (p.snd ≫ s.π k) = t.π k.succ
        rw [← Category.assoc, consLift_snd, tailLift_π])
    (by
      intro t m hbase hπ
      apply (IsPullback.of_isLimit hp).hom_ext
      · change m ≫ p.fst = consLift f s p hs hp t ≫ p.fst
        rw [consLift_fst]
        exact hπ 0
      · change m ≫ p.snd = consLift f s p hs hp t ≫ p.snd
        rw [consLift_snd]
        apply WidePullbackCone.IsLimit.hom_ext hs
        · rw [tailLift_base, Category.assoc, ← p.condition]
          exact hbase
        · intro j
          rw [tailLift_π, Category.assoc]
          exact hπ j.succ)

end Langlands.FiniteWidePullback
