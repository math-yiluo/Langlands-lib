import Langlands.Topology.LocallyConstant.CoveringTrace
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.SetTheory.Cardinal.Finite

/-! # Actual fiber reindexing for compact-function correspondences -/

noncomputable section

universe u w

namespace Langlands.LocallyConstantCovering

open CategoryTheory Limits

variable {S X Y Z : Type u} {V : Type w} [AddCommGroup V]

/-- The trace of a precomposition counts the entire original fiber. -/
theorem fiberSum_comap (q : X → Y) [∀ y, Finite (q ⁻¹' {y})]
    (f : Y → V) (y : Y) :
    fiberSum q (f ∘ q) y = Nat.card (q ⁻¹' {y}) • f y := by
  classical
  let := Fintype.ofFinite (q ⁻¹' {y})
  simp only [fiberSum, Function.comp_apply]
  calc
    (∑ x : q ⁻¹' {y}, f (q x.val)) = ∑ _x : q ⁻¹' {y}, f y := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg f x.property
    _ = Nat.card (q ⁻¹' {y}) • f y := by
      simp [Nat.card_eq_fintype_card]

/-- A genuine pullback square of the original maps identifies its literal
fibers by its first projection. -/
def pullbackFiberEquiv (a : S → X) (b : S → Y) (q : X → Z) (p : Y → Z)
    (h : IsPullback (↾a) (↾b) (↾q) (↾p)) (y : Y) :
    b ⁻¹' {y} ≃ q ⁻¹' {p y} :=
  Equiv.ofBijective
    (fun s => ⟨a s.val,
      (show q (a s.val) = p (b s.val) from ConcreteCategory.congr_hom h.w s.val).trans
        (congrArg p (show b s.val = y from s.property))⟩)
    ⟨by
      intro s t hst
      apply Subtype.ext
      exact Types.ext_of_isPullback h (congrArg Subtype.val hst)
        (s.property.trans t.property.symm),
    by
      intro x
      obtain ⟨s, hs, hy⟩ := Types.exists_of_isPullback h x.val y x.property
      exact ⟨⟨s, hy⟩, Subtype.ext hs⟩⟩

@[simp]
theorem pullbackFiberEquiv_apply (a : S → X) (b : S → Y) (q : X → Z) (p : Y → Z)
    (h : IsPullback (↾a) (↾b) (↾q) (↾p)) (y : Y) (s : b ⁻¹' {y}) :
    (pullbackFiberEquiv a b q p h y s).val = a s.val := rfl

/-- Finite original fibers remain finite in every actual pullback square. -/
theorem finite_pullback_fiber (a : S → X) (b : S → Y) (q : X → Z) (p : Y → Z)
    (h : IsPullback (↾a) (↾b) (↾q) (↾p))
    [∀ z, Finite (q ⁻¹' {z})] (y : Y) : Finite (b ⁻¹' {y}) :=
  Finite.of_equiv (q ⁻¹' {p y}) (pullbackFiberEquiv a b q p h y).symm

/-- Base change is proved by reindexing the actual finite fibers, with no
assumed trace-compatibility equation. -/
theorem fiberSum_baseChange (a : S → X) (b : S → Y) (q : X → Z) (p : Y → Z)
    (h : IsPullback (↾a) (↾b) (↾q) (↾p))
    [∀ z, Finite (q ⁻¹' {z})] [∀ y, Finite (b ⁻¹' {y})]
    (f : X → V) (y : Y) :
    fiberSum b (f ∘ a) y = fiberSum q f (p y) := by
  let := Fintype.ofFinite (b ⁻¹' {y})
  let := Fintype.ofFinite (q ⁻¹' {p y})
  exact Fintype.sum_equiv (pullbackFiberEquiv a b q p h y) _ _ (fun _ => rfl)

/-- The canonical product subtype is an actual pullback, by Mathlib's
constructed limiting cone. -/
theorem isPullback_prodSubtype (q : X → Z) (p : Y → Z) :
    IsPullback
      (↾fun s : Types.PullbackObj (↾q) (↾p) => s.val.1)
      (↾fun s : Types.PullbackObj (↾q) (↾p) => s.val.2) (↾q) (↾p) :=
  IsPullback.of_isLimit (Types.pullbackLimitCone (↾q) (↾p)).isLimit

/-- Composition of spans is the trace along the original composite on their
actual pullback, by finite-sum composition and cartesian fiber reindexing. -/
theorem fiberSum_pullback_comp {T W : Type u}
    (e : W → S) (f : W → T) (b : S → Y) (c : T → Y) (d : T → Z)
    (h : IsPullback (↾e) (↾f) (↾b) (↾c))
    [∀ y, Finite (b ⁻¹' {y})] [∀ t, Finite (f ⁻¹' {t})]
    [∀ z, Finite (d ⁻¹' {z})] [∀ z, Finite ((d ∘ f) ⁻¹' {z})]
    (s : S → V) (z : Z) :
    fiberSum (d ∘ f) (s ∘ e) z =
      fiberSum d (fun t => fiberSum b s (c t)) z := by
  rw [fiberSum_comp]
  exact congrArg (fun k : T → V => fiberSum d k z)
    (funext (fun t => fiberSum_baseChange e f b c h s t))

end Langlands.LocallyConstantCovering
