import Langlands.GroupScheme.Rational.InnerDiscrepancyOverlap
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Fppf descent of points representing inner discrepancies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}
  (e : LocalGroupIso G H U) (a : AutomorphicAction A G)

/-- The discrepancy equation can be checked after an fppf cover of its test. -/
theorem representsDiscrepancy_of_fppf_cover {T V : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    {b c : T ⟶ U} {x : T ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) (p ≫ x)) :
    e.RepresentsDiscrepancy a b c x := by
  intro W t g
  let Z : Over S := Over.mk (pullback.fst t.left p.left ≫ W.hom)
  let r : Z ⟶ W := Over.homMk (pullback.fst t.left p.left) rfl
  let s : Z ⟶ V := Over.homMk (pullback.snd t.left p.left) (by
    rw [← Over.w p, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w t]
    rfl)
  have hrs : r ≫ t = s ≫ p := Over.OverMorphism.ext pullback.condition
  have : Epi r.left := by
    change Epi (pullback.fst t.left p.left)
    infer_instance
  have : Epi r := Over.epi_of_epi_left r
  apply (cancel_epi r).mp
  rw [← e.naturality, ← e.naturality, a.naturality]
  simpa only [← Category.assoc, hrs] using hx s (r ≫ g)

variable (ha : a.IsFaithful)

include ha

/-- Faithfulness makes local representatives agree on the relation of a cover. -/
theorem representative_relation {T V : Over S} (p : V ⟶ T)
    {b c : T ⟶ U} {x : V ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x)
    {W : Over S} (r s : W ⟶ V) (hrs : r ≫ p = s ≫ p) :
    r ≫ x = s ≫ x := by
  apply RepresentsDiscrepancy.unique e a ha
    (RepresentsDiscrepancy.comp e a hx r)
  have hb : r ≫ (p ≫ b) = s ≫ (p ≫ b) := by
    rw [← Category.assoc, hrs, Category.assoc]
  have hc : r ≫ (p ≫ c) = s ≫ (p ≫ c) := by
    rw [← Category.assoc, hrs, Category.assoc]
  intro Z t g
  rw [hb, hc]
  exact RepresentsDiscrepancy.comp e a hx s t g

/-- Compatibility of a local representative also holds for maps of schemes. -/
theorem representative_scheme_relation {T V : Over S} (p : V ⟶ T)
    {b c : T ⟶ U} {x : V ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x)
    {Z : Scheme.{u}} (r s : Z ⟶ V.left)
    (hrs : r ≫ p.left = s ≫ p.left) : r ≫ x.left = s ≫ x.left := by
  have hs : s ≫ V.hom = r ≫ V.hom := by
    rw [← Over.w p, ← Category.assoc, ← Category.assoc, hrs]
  let r₀ : Over.mk (r ≫ V.hom) ⟶ V := Over.homMk r rfl
  let s₀ : Over.mk (r ≫ V.hom) ⟶ V := Over.homMk s hs
  exact congrArg (fun f => f.left)
    (e.representative_relation a ha p hx r₀ s₀ (Over.OverMorphism.ext hrs))

/-- The actual point obtained by effective descent of a local discrepancy
representative along an fppf cover. -/
def fppfDescendedRepresentative {T V : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    {b c : T ⟶ U} (x : V ⟶ A.X)
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x) : T ⟶ A.X := by
  let hrel := fun {Z : Scheme.{u}} (r s : Z ⟶ V.left)
    (hrs : r ≫ p.left = s ≫ p.left) =>
      e.representative_scheme_relation a ha p hx r s hrs
  let y₀ : T.left ⟶ A.X.left := EffectiveEpi.desc p.left x.left hrel
  have hy₀ : p.left ≫ y₀ = x.left := EffectiveEpi.fac p.left x.left hrel
  exact Over.homMk y₀ (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hy₀, Over.w x, Over.w p])

/-- The descended representative pulls back to the given local point. -/
theorem fppfDescendedRepresentative_pullback {T V : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    {b c : T ⟶ U} (x : V ⟶ A.X)
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x) :
    p ≫ e.fppfDescendedRepresentative a ha p x hx = x := by
  apply Over.OverMorphism.ext
  exact EffectiveEpi.fac p.left x.left
    (fun r s hrs => e.representative_scheme_relation a ha p hx r s hrs)

/-- The descended point represents the original discrepancy on every refinement. -/
theorem fppfDescendedRepresentative_spec {T V : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    {b c : T ⟶ U} (x : V ⟶ A.X)
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x) :
    e.RepresentsDiscrepancy a b c (e.fppfDescendedRepresentative a ha p x hx) := by
  apply e.representsDiscrepancy_of_fppf_cover a p
  rwa [e.fppfDescendedRepresentative_pullback a ha p x hx]

/-- A point representing the discrepancy on an fppf cover descends to a point
representing it on the original test scheme. -/
theorem exists_representsDiscrepancy_of_fppf_cover {T V : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    {b c : T ⟶ U} (x : V ⟶ A.X)
    (hx : e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x) :
    ∃ y : T ⟶ A.X, p ≫ y = x ∧ e.RepresentsDiscrepancy a b c y :=
  ⟨e.fppfDescendedRepresentative a ha p x hx,
    e.fppfDescendedRepresentative_pullback a ha p x hx,
    e.fppfDescendedRepresentative_spec a ha p x hx⟩

/-- Existence of an all-refinement discrepancy point is fppf-local on the test. -/
theorem exists_representsDiscrepancy_iff_fppf_cover {T V : Over S} (p : V ⟶ T)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    (b c : T ⟶ U) :
    (∃ y : T ⟶ A.X, e.RepresentsDiscrepancy a b c y) ↔
      ∃ x : V ⟶ A.X, e.RepresentsDiscrepancy a (p ≫ b) (p ≫ c) x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨p ≫ y, RepresentsDiscrepancy.comp e a hy p⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, -, hy⟩ := e.exists_representsDiscrepancy_of_fppf_cover a ha p x hx
    exact ⟨y, hy⟩

/-- An inner representative over one fppf cover of the universal overlap
supplies inner discrepancy on all tests. -/
theorem hasInnerDiscrepancy_of_fppf_overlap {V : Over S} (p : V ⟶ U ⊗ U)
    [Flat p.left] [Surjective p.left] [LocallyOfFinitePresentation p.left]
    (x : V ⟶ A.X)
    (hx : e.RepresentsDiscrepancy a (p ≫ fst U U) (p ≫ snd U U) x) :
    e.HasInnerDiscrepancy a := by
  obtain ⟨y, -, hy⟩ := e.exists_representsDiscrepancy_of_fppf_cover a ha p x hx
  apply (e.hasInnerDiscrepancy_iff_overlap a).mpr
  exact ⟨y, hy (fst (U ⊗ U) G.X) (snd (U ⊗ U) G.X)⟩

end Langlands.GroupScheme.LocalGroupIso
