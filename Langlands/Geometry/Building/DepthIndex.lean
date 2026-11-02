import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.NormNum.Basic

/-! # The Kaletha–Prasad depth monoid of real, strict and infinite depths -/

noncomputable section

namespace Langlands.Geometry.Building

/-- A finite depth: the real depth `re` when `strict = false`, and the strict depth `re+`
when `strict = true`. -/
@[ext]
structure FiniteDepth where
  /-- The real part of the depth. -/
  re : ℝ
  /-- The strict flag; it is `true` exactly for `re+`. -/
  strict : Bool

namespace FiniteDepth

/-- The lexicographic encoding `x ↦ (x.re, x.strict)` in `ℝ ×ₗ Bool`. -/
def toLexPair (x : FiniteDepth) : ℝ ×ₗ Bool :=
  toLex (x.re, x.strict)

theorem toLexPair_injective : Function.Injective toLexPair := by
  rintro ⟨r, a⟩ ⟨s, b⟩ h
  have h' := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  rw [h'.1, h'.2]

/-- The lexicographic order, with the ordinary flag `false` below the strict flag `true`. -/
instance : LinearOrder FiniteDepth :=
  LinearOrder.lift' toLexPair toLexPair_injective

theorem le_iff {x y : FiniteDepth} :
    x ≤ y ↔ x.re < y.re ∨ x.re = y.re ∧ x.strict ≤ y.strict :=
  Prod.Lex.toLex_le_toLex

theorem lt_iff {x y : FiniteDepth} :
    x < y ↔ x.re < y.re ∨ x.re = y.re ∧ x.strict < y.strict :=
  Prod.Lex.toLex_lt_toLex

/-- Addition adds the real parts and takes the logical or of the strict flags. -/
instance : Add FiniteDepth :=
  ⟨fun x y => ⟨x.re + y.re, x.strict || y.strict⟩⟩

/-- The ordinary real depth `0`. -/
instance : Zero FiniteDepth :=
  ⟨⟨0, false⟩⟩

@[simp] theorem add_re (x y : FiniteDepth) : (x + y).re = x.re + y.re := rfl

@[simp] theorem add_strict (x y : FiniteDepth) : (x + y).strict = (x.strict || y.strict) := rfl

@[simp] theorem zero_re : (0 : FiniteDepth).re = 0 := rfl

@[simp] theorem zero_strict : (0 : FiniteDepth).strict = false := rfl

instance : AddCommMonoid FiniteDepth where
  add_assoc x y z := by ext <;> simp [add_assoc, Bool.or_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm, Bool.or_comm]
  nsmul := nsmulRec

instance : IsOrderedAddMonoid FiniteDepth where
  add_le_add_left x y h z := by
    rw [le_iff] at h ⊢
    simp only [add_re, add_strict]
    rcases h with h | ⟨h₁, h₂⟩
    · exact Or.inl (add_lt_add_of_lt_of_le h le_rfl)
    · refine Or.inr ⟨by rw [h₁], ?_⟩
      revert h₂
      cases x.strict <;> cases y.strict <;> cases z.strict <;> decide

/-- The strict depth with the same real part. -/
def plus (x : FiniteDepth) : FiniteDepth :=
  ⟨x.re, true⟩

theorem monotone_plus : Monotone plus := by
  intro x y h
  rw [le_iff] at h ⊢
  rcases h with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, le_rfl⟩

theorem le_plus (x : FiniteDepth) : x ≤ plus x :=
  le_iff.2 (Or.inr ⟨rfl, Bool.le_true _⟩)

end FiniteDepth

/-- The corrected Kaletha–Prasad depth set `ℝ̃ = (ℝ × {0, 1}) ∪ {∞}` of §1.6: a finite part
`FiniteDepth` together with the greatest element `⊤ = ∞`. -/
def DepthIndex : Type :=
  WithTop FiniteDepth

namespace DepthIndex

instance : AddCommMonoid DepthIndex :=
  inferInstanceAs (AddCommMonoid (WithTop FiniteDepth))

instance : LinearOrder DepthIndex :=
  inferInstanceAs (LinearOrder (WithTop FiniteDepth))

instance : OrderTop DepthIndex :=
  inferInstanceAs (OrderTop (WithTop FiniteDepth))

instance : IsOrderedAddMonoid DepthIndex :=
  inferInstanceAs (IsOrderedAddMonoid (WithTop FiniteDepth))

/-! ### Constructors and cases -/

/-- The finite depth `x`, regarded in `ℝ̃`. -/
def ofFinite (x : FiniteDepth) : DepthIndex :=
  WithTop.some x

/-- The ordinary real depth `r`, the pair `(r, 0)`. -/
def ord (r : ℝ) : DepthIndex :=
  ofFinite ⟨r, false⟩

/-- The strict depth `r+`, the pair `(r, 1)`. -/
def strict (r : ℝ) : DepthIndex :=
  ofFinite ⟨r, true⟩

theorem ofFinite_injective : Function.Injective ofFinite :=
  WithTop.coe_injective

@[simp] theorem ofFinite_inj {x y : FiniteDepth} : ofFinite x = ofFinite y ↔ x = y :=
  ofFinite_injective.eq_iff

@[simp] theorem ofFinite_ne_top (x : FiniteDepth) : ofFinite x ≠ ⊤ :=
  WithTop.coe_ne_top

theorem ofFinite_mk (r : ℝ) (b : Bool) :
    ofFinite ⟨r, b⟩ = if b then strict r else ord r := by
  cases b <;> rfl

theorem ord_injective : Function.Injective ord := by
  intro r s h
  have := congrArg FiniteDepth.re (ofFinite_injective h)
  exact this

theorem strict_injective : Function.Injective strict := by
  intro r s h
  have := congrArg FiniteDepth.re (ofFinite_injective h)
  exact this

@[simp] theorem ord_inj {r s : ℝ} : ord r = ord s ↔ r = s :=
  ord_injective.eq_iff

@[simp] theorem strict_inj {r s : ℝ} : strict r = strict s ↔ r = s :=
  strict_injective.eq_iff

@[simp] theorem ord_ne_strict (r s : ℝ) : ord r ≠ strict s := by
  intro h
  have := congrArg FiniteDepth.strict (ofFinite_injective h)
  exact Bool.false_ne_true this

@[simp] theorem strict_ne_ord (r s : ℝ) : strict r ≠ ord s :=
  (ord_ne_strict s r).symm

@[simp] theorem ord_ne_top (r : ℝ) : ord r ≠ ⊤ :=
  ofFinite_ne_top _

@[simp] theorem strict_ne_top (r : ℝ) : strict r ≠ ⊤ :=
  ofFinite_ne_top _

@[simp] theorem top_ne_ord (r : ℝ) : ⊤ ≠ ord r :=
  (ord_ne_top r).symm

@[simp] theorem top_ne_strict (r : ℝ) : ⊤ ≠ strict r :=
  (strict_ne_top r).symm

/-- Every depth is an ordinary real depth, a strict real depth, or `∞`. -/
theorem exists_eq_ord_or_strict_or_top (x : DepthIndex) :
    (∃ r, x = ord r) ∨ (∃ r, x = strict r) ∨ x = ⊤ := by
  induction x using WithTop.recTopCoe with
  | top => exact Or.inr (Or.inr rfl)
  | coe x =>
    obtain ⟨r, b⟩ := x
    cases b
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨r, rfl⟩)

/-- Case analysis on depths: ordinary, strict and infinite. -/
@[elab_as_elim]
protected theorem ind {motive : DepthIndex → Prop} (ord : ∀ r, motive (DepthIndex.ord r))
    (strict : ∀ r, motive (DepthIndex.strict r)) (top : motive ⊤) (x : DepthIndex) :
    motive x := by
  rcases exists_eq_ord_or_strict_or_top x with ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl
  · exact ord r
  · exact strict r
  · exact top

/-! ### Order -/

theorem ofFinite_le_ofFinite {x y : FiniteDepth} : ofFinite x ≤ ofFinite y ↔ x ≤ y :=
  WithTop.coe_le_coe

theorem ofFinite_lt_ofFinite {x y : FiniteDepth} : ofFinite x < ofFinite y ↔ x < y :=
  WithTop.coe_lt_coe

@[simp] theorem ofFinite_lt_top (x : FiniteDepth) : ofFinite x < ⊤ :=
  WithTop.coe_lt_top x

@[simp] theorem ord_le_ord {r s : ℝ} : ord r ≤ ord s ↔ r ≤ s := by
  rw [ord, ord, ofFinite_le_ofFinite, FiniteDepth.le_iff]
  simp [le_iff_lt_or_eq]

@[simp] theorem ord_lt_ord {r s : ℝ} : ord r < ord s ↔ r < s := by
  rw [ord, ord, ofFinite_lt_ofFinite, FiniteDepth.lt_iff]
  simp

@[simp] theorem strict_le_strict {r s : ℝ} : strict r ≤ strict s ↔ r ≤ s := by
  rw [strict, strict, ofFinite_le_ofFinite, FiniteDepth.le_iff]
  simp [le_iff_lt_or_eq]

@[simp] theorem strict_lt_strict {r s : ℝ} : strict r < strict s ↔ r < s := by
  rw [strict, strict, ofFinite_lt_ofFinite, FiniteDepth.lt_iff]
  simp

/-- `r ≤ s+` exactly when `r ≤ s`. -/
@[simp] theorem ord_le_strict {r s : ℝ} : ord r ≤ strict s ↔ r ≤ s := by
  rw [ord, strict, ofFinite_le_ofFinite, FiniteDepth.le_iff]
  simp [le_iff_lt_or_eq]

/-- `r < s+` exactly when `r ≤ s`. -/
@[simp] theorem ord_lt_strict {r s : ℝ} : ord r < strict s ↔ r ≤ s := by
  rw [ord, strict, ofFinite_lt_ofFinite, FiniteDepth.lt_iff]
  simp [le_iff_lt_or_eq]

/-- `r+ ≤ s` exactly when `r < s`. -/
@[simp] theorem strict_le_ord {r s : ℝ} : strict r ≤ ord s ↔ r < s := by
  rw [strict, ord, ofFinite_le_ofFinite, FiniteDepth.le_iff]
  simp

/-- `r+ < s` exactly when `r < s`. -/
@[simp] theorem strict_lt_ord {r s : ℝ} : strict r < ord s ↔ r < s := by
  rw [strict, ord, ofFinite_lt_ofFinite, FiniteDepth.lt_iff]
  simp

/-- The strict depth `r+` is strictly larger than `r`. -/
theorem ord_lt_strict_self (r : ℝ) : ord r < strict r :=
  ord_lt_strict.2 le_rfl

@[simp] theorem ord_lt_top (r : ℝ) : ord r < ⊤ :=
  ofFinite_lt_top _

@[simp] theorem strict_lt_top (r : ℝ) : strict r < ⊤ :=
  ofFinite_lt_top _

@[simp] theorem le_top' (x : DepthIndex) : x ≤ ⊤ :=
  le_top

@[simp] theorem top_le_iff' {x : DepthIndex} : ⊤ ≤ x ↔ x = ⊤ :=
  top_le_iff

@[simp] theorem not_top_le_ord (r : ℝ) : ¬ (⊤ : DepthIndex) ≤ ord r :=
  not_le.2 (ord_lt_top r)

@[simp] theorem not_top_le_strict (r : ℝ) : ¬ (⊤ : DepthIndex) ≤ strict r :=
  not_le.2 (strict_lt_top r)

theorem lt_top_iff {x : DepthIndex} : x < ⊤ ↔ x ≠ ⊤ :=
  lt_top_iff_ne_top

/-- For `r < s`, the chain `r < r+ < s < s+`. -/
theorem ord_lt_strict_lt_ord_lt_strict {r s : ℝ} (h : r < s) :
    ord r < strict r ∧ strict r < ord s ∧ ord s < strict s :=
  ⟨ord_lt_strict_self r, strict_lt_ord.2 h, ord_lt_strict_self s⟩

theorem strictMono_ord : StrictMono ord :=
  fun _ _ h => ord_lt_ord.2 h

theorem strictMono_strict : StrictMono strict :=
  fun _ _ h => strict_lt_strict.2 h

/-- The ordinary real inclusion `r ↦ r` as an order embedding. -/
def ordOrderEmbedding : ℝ ↪o DepthIndex :=
  OrderEmbedding.ofStrictMono ord strictMono_ord

@[simp] theorem ordOrderEmbedding_apply (r : ℝ) : ordOrderEmbedding r = ord r := rfl

/-- The strict inclusion `r ↦ r+` as an order embedding. -/
def strictOrderEmbedding : ℝ ↪o DepthIndex :=
  OrderEmbedding.ofStrictMono strict strictMono_strict

@[simp] theorem strictOrderEmbedding_apply (r : ℝ) : strictOrderEmbedding r = strict r := rfl

/-! ### Addition -/

theorem ofFinite_add (x y : FiniteDepth) : ofFinite (x + y) = ofFinite x + ofFinite y := rfl

theorem zero_def : (0 : DepthIndex) = ord 0 := rfl

@[simp] theorem ord_zero : ord 0 = 0 := rfl

@[simp] theorem ord_add_ord (r s : ℝ) : ord r + ord s = ord (r + s) := rfl

@[simp] theorem ord_add_strict (r s : ℝ) : ord r + strict s = strict (r + s) := rfl

@[simp] theorem strict_add_ord (r s : ℝ) : strict r + ord s = strict (r + s) := rfl

@[simp] theorem strict_add_strict (r s : ℝ) : strict r + strict s = strict (r + s) := rfl

@[simp] protected theorem top_add (x : DepthIndex) : ⊤ + x = ⊤ :=
  WithTop.top_add x

@[simp] protected theorem add_top (x : DepthIndex) : x + ⊤ = ⊤ :=
  WithTop.add_top x

theorem add_monotone_left (x : DepthIndex) : Monotone (x + ·) :=
  fun _ _ h => add_le_add le_rfl h

theorem add_monotone_right (y : DepthIndex) : Monotone (· + y) :=
  fun _ _ h => add_le_add h le_rfl

/-- The ordinary real inclusion `r ↦ r` as an additive monoid homomorphism. -/
def ordAddMonoidHom : ℝ →+ DepthIndex where
  toFun := ord
  map_zero' := rfl
  map_add' r s := (ord_add_ord r s).symm

@[simp] theorem ordAddMonoidHom_apply (r : ℝ) : ordAddMonoidHom r = ord r := rfl

theorem ord_add (r s : ℝ) : ord (r + s) = ord r + ord s :=
  (ord_add_ord r s).symm

/-! ### The plus operation -/

/-- The operation `x ↦ x+`: it sends `r` to `r+`, fixes `r+`, and fixes `∞`. -/
def plus : DepthIndex → DepthIndex :=
  WithTop.map FiniteDepth.plus

@[simp] theorem plus_ord (r : ℝ) : plus (ord r) = strict r := rfl

@[simp] theorem plus_strict (r : ℝ) : plus (strict r) = strict r := rfl

@[simp] theorem plus_top : plus ⊤ = ⊤ := rfl

theorem monotone_plus : Monotone plus :=
  FiniteDepth.monotone_plus.withTop_map

theorem le_plus (x : DepthIndex) : x ≤ plus x := by
  induction x using DepthIndex.ind with
  | ord r => exact (ord_lt_strict_self r).le
  | strict r => exact le_rfl
  | top => exact le_rfl

@[simp] theorem plus_plus (x : DepthIndex) : plus (plus x) = plus x := by
  induction x using DepthIndex.ind with
  | ord r => rfl
  | strict r => rfl
  | top => rfl

end DepthIndex

namespace DepthIndex.Example

/-- Negative real depths are ordinary depths below `0`. -/
theorem ord_neg_one_lt_zero : ord (-1) < (0 : DepthIndex) := by
  rw [← ord_zero, ord_lt_ord]
  norm_num

/-- For `r < s`, the strict depth `r+` lies strictly between `r` and `s`. -/
theorem ord_lt_strict_lt_ord {r s : ℝ} (h : r < s) : ord r < strict r ∧ strict r < ord s :=
  ⟨ord_lt_strict_self r, strict_lt_ord.2 h⟩

/-- Concretely, `-1 < (-1)+ < 0`. -/
theorem ord_neg_one_lt_strict_neg_one_lt_zero :
    ord (-1) < strict (-1) ∧ strict (-1) < (0 : DepthIndex) := by
  rw [← ord_zero]
  exact ord_lt_strict_lt_ord (by norm_num)

/-- Zero and strict zero are distinct. -/
theorem zero_ne_strict_zero : (0 : DepthIndex) ≠ strict 0 :=
  ord_ne_strict 0 0

theorem zero_lt_strict_zero : (0 : DepthIndex) < strict 0 :=
  ord_lt_strict_self 0

/-- Adding two strict depths gives a strict depth. -/
theorem strict_one_add_strict_neg_two : strict 1 + strict (-2) = strict (-1) := by
  rw [strict_add_strict, strict_inj]
  norm_num

/-- `∞` absorbs every depth. -/
theorem strict_neg_one_add_top : strict (-1) + ⊤ = ⊤ :=
  DepthIndex.add_top _

theorem top_add_ord_neg_one : ⊤ + ord (-1) = ⊤ :=
  DepthIndex.top_add _

/-- The plus operation is idempotent; on `0` it gives `0+`. -/
theorem plus_plus_zero : plus (plus (0 : DepthIndex)) = strict 0 := by
  rw [plus_plus, ← ord_zero, plus_ord]

/-- The plus operation does not preserve zero. -/
theorem plus_zero_ne_zero : plus (0 : DepthIndex) ≠ 0 := by
  rw [← ord_zero, plus_ord]
  exact strict_ne_ord 0 0

/-- Adding strict zero identifies `r` and `r+`, so addition is not cancellative. -/
theorem strict_zero_add_ord (r : ℝ) : strict 0 + ord r = strict 0 + strict r := by
  simp

theorem not_isAddLeftRegular_strict_zero : ¬ IsAddLeftRegular (strict 0) := by
  intro h
  exact ord_ne_strict 0 0 (h (strict_zero_add_ord 0))

/-- Translation by strict zero is monotone but not strictly monotone. -/
theorem not_strictMono_strict_zero_add : ¬ StrictMono (strict 0 + ·) := by
  intro h
  exact (h (ord_lt_strict_self 0)).ne (strict_zero_add_ord 0)

/-- Translation by `∞` identifies all depths. -/
theorem top_add_ord_eq_top_add_strict (r s : ℝ) : ⊤ + ord r = ⊤ + strict s := by
  simp

/-- Not every depth is nonnegative, so the order is not canonical for addition. -/
theorem not_forall_zero_le : ¬ ∀ x : DepthIndex, 0 ≤ x :=
  fun h => not_le.2 ord_neg_one_lt_zero (h _)

end DepthIndex.Example

end Langlands.Geometry.Building
