import Langlands.GroupScheme.HomogeneousQuotientComparison

/-! # Monomorphisms descended from identical all-test fibers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.HomogeneousQuotientComparison

variable {S : Scheme.{u}} {X Q R : Over S} (q : X ⟶ Q) (r : X ⟶ R)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]

/-- Equality of relative maps can be tested on fpqc local lifts through `q`. -/
theorem hom_ext_of_local_lift {T Y : Over S} (x : T ⟶ Q) (f g : T ⟶ Y)
    (h : ∀ (V : Over S) (v : V ⟶ T) (a : V ⟶ X),
      v ≫ x = a ≫ q → v ≫ f = v ≫ g) : f = g := by
  let V : Over S := Over.mk (pullback.fst x.left q.left ≫ T.hom)
  let v : V ⟶ T := Over.homMk (pullback.fst x.left q.left) rfl
  let a : V ⟶ X := Over.homMk (pullback.snd x.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x]
    rfl)
  have : Epi v.left := by
    change Epi (pullback.fst x.left q.left)
    infer_instance
  have : Epi v := Over.epi_of_epi_left v
  apply (cancel_epi v).mp
  exact h V v a (Over.OverMorphism.ext pullback.condition)

/-- If `r` and the fpqc map `q` have identical fibers on every relative test,
the induced map out of `Q` is a scheme monomorphism. -/
theorem mono_desc_of_fiber_iff
    (h : ∀ (T : Over S) (a b : T ⟶ X),
      a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r) :
    Mono (desc q r (fun T a b hab => (h T a b).mp hab)).left := by
  let d := desc q r (fun T a b hab => (h T a b).mp hab)
  have hd : q ≫ d = r := fac_desc q r _
  have : Mono d := by
    constructor
    intro T a b hab
    apply hom_ext_of_local_lift q a a b
    intro V v a' ha
    apply hom_ext_of_local_lift q (v ≫ b) (v ≫ a) (v ≫ b)
    intro W w b' hb
    have he : (w ≫ a') ≫ r = b' ≫ r := by
      calc
        (w ≫ a') ≫ r = w ≫ (a' ≫ q) ≫ d := by
          rw [← hd]
          simp only [Category.assoc]
        _ = w ≫ (v ≫ a) ≫ d := by rw [← ha]
        _ = w ≫ (v ≫ b) ≫ d := by
          simpa only [Category.assoc] using congrArg (fun z => w ≫ v ≫ z) hab
        _ = b' ≫ r := by
          rw [← hd]
          simpa only [Category.assoc] using congrArg (fun z => z ≫ d) hb
    have he' := (h W (w ≫ a') b').mpr he
    simpa only [Category.assoc, ← ha, ← hb] using he'
  exact Over.mono_left_of_mono d

end Langlands.GroupScheme.HomogeneousQuotientComparison
