import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Finite local lifting for ordered products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false

/-- A simultaneous lift of a finite family after an fppf change of test scheme. -/
structure FppfLiftFamily {n : ℕ} (X Y : Fin n → Over B)
    (p : ∀ i, X i ⟶ Y i) (T : Over B) (y : ∀ i, T ⟶ Y i) where
  cover : Over B
  map : cover ⟶ T
  flat : Flat map.left
  surjective : Surjective map.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation map.left
  lift : ∀ i, cover ⟶ X i
  commutes : ∀ i, map ≫ y i = lift i ≫ p i

/-- Finitely many points lift simultaneously after an fppf change of test scheme. -/
theorem exists_fppf_lift_family (n : ℕ) :
    ∀ (X Y : Fin n → Over B) (p : ∀ i, X i ⟶ Y i),
      (∀ i, Flat (p i).left) → (∀ i, Surjective (p i).left) →
      (∀ i, LocallyOfFinitePresentation (p i).left) →
      ∀ (T : Over B) (y : ∀ i, T ⟶ Y i),
        ∃ (V : Over B) (a : V ⟶ T),
          Flat a.left ∧ Surjective a.left ∧ LocallyOfFinitePresentation a.left ∧
          ∃ x : ∀ i, V ⟶ X i, ∀ i, a ≫ y i = x i ≫ p i := by
  induction n with
  | zero =>
      intro X Y p hf hs hl T y
      exact ⟨T, 𝟙 T, by change Flat (𝟙 T.left); infer_instance,
        by change Surjective (𝟙 T.left); infer_instance,
        by change LocallyOfFinitePresentation (𝟙 T.left); infer_instance,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro X Y p hf hs hl T y
      let := hf 0
      let := hs 0
      let := hl 0
      let W : Over B := Over.mk (pullback.fst (y 0).left (p 0).left ≫ T.hom)
      let a : W ⟶ T := Over.homMk (pullback.fst (y 0).left (p 0).left) rfl
      let x₀ : W ⟶ X 0 := Over.homMk (pullback.snd (y 0).left (p 0).left) (by
        rw [← Over.w (p 0), ← Category.assoc, ← pullback.condition,
          Category.assoc, Over.w (y 0)]
        rfl)
      have ha : a ≫ y 0 = x₀ ≫ p 0 :=
        Over.OverMorphism.ext pullback.condition
      obtain ⟨V, b, hbf, hbs, hbl, x, hx⟩ := ih
        (fun i => X i.succ) (fun i => Y i.succ) (fun i => p i.succ)
        (fun i => hf i.succ) (fun i => hs i.succ) (fun i => hl i.succ)
        W (fun i => a ≫ y i.succ)
      let := hbf
      let := hbs
      let := hbl
      have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
      have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
      have : LocallyOfFinitePresentation a.left := by
        change LocallyOfFinitePresentation (pullback.fst _ _)
        infer_instance
      refine ⟨V, b ≫ a, ?_, ?_, ?_,
        Fin.cases (b ≫ x₀) x, ?_⟩
      · change Flat (b.left ≫ a.left); infer_instance
      · change Surjective (b.left ≫ a.left); infer_instance
      · change LocallyOfFinitePresentation (b.left ≫ a.left); infer_instance
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Category.assoc, Fin.cases_zero] using congrArg (b ≫ ·) ha
        · simpa only [Category.assoc, Fin.cases_succ] using hx j

/-- Flat surjections locally of finite presentation admit simultaneous finite lifts. -/
theorem nonempty_fppfLiftFamily {n : ℕ} (X Y : Fin n → Over B)
    (p : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, Flat (p i).left) (hs : ∀ i, Surjective (p i).left)
    (hl : ∀ i, LocallyOfFinitePresentation (p i).left)
    (T : Over B) (y : ∀ i, T ⟶ Y i) :
    Nonempty (FppfLiftFamily X Y p T y) := by
  obtain ⟨V, a, haf, has, hal, x, hx⟩ :=
    exists_fppf_lift_family n X Y p hf hs hl T y
  exact ⟨⟨V, a, haf, has, hal, x, hx⟩⟩

/-- A monomorphism is an isomorphism if an effective cover of its target factors
through it. This lets local lifts produce a scheme isomorphism. -/
theorem isIso_of_effectiveEpi_factorization {X Y V : Over B} (m : X ⟶ Y)
    [Mono m] (a : V ⟶ Y) [EffectiveEpi a.left] (x : V ⟶ X)
    (hx : x ≫ m = a) : IsIso m := by
  have : EffectiveEpi (x.left ≫ m.left) := by
    change EffectiveEpi (x ≫ m).left
    rw [hx]
    infer_instance
  have : StrongEpi m.left := strongEpi_of_strongEpi x.left m.left
  have : IsIso ((Over.forget B).map m) := isIso_of_mono_of_strongEpi m.left
  exact isIso_of_reflects_iso m (Over.forget B)

end Langlands.GroupScheme.RelativeRoot
