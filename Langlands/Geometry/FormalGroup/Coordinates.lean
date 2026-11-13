import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Pointed maps in formal coordinates

Finite tuples of power series with zero constant term, with composition and
evaluation on tuples whose constant coefficients are nilpotent.
-/

noncomputable section

universe u

namespace Langlands.FormalGroup

open MvPowerSeries

variable {R : Type u} [CommRing R]
variable {σ τ υ ω κ : Type}

/-- A pointed formal map from the formal affine space with coordinates `σ`
to the one with coordinates `τ`. -/
@[ext]
structure CoordinateMap (R : Type u) [CommRing R] (σ τ : Type) where
  series : τ → MvPowerSeries σ R
  constantCoeff_eq_zero : ∀ i, (series i).constantCoeff = 0

namespace CoordinateMap

theorem hasSubst [Finite τ] (f : CoordinateMap R σ τ) : HasSubst f.series :=
  hasSubst_of_constantCoeff_zero f.constantCoeff_eq_zero

/-- The identity pointed formal map. -/
def id : CoordinateMap R σ σ where
  series := X
  constantCoeff_eq_zero := constantCoeff_X

/-- The zero pointed formal map. -/
def zero : CoordinateMap R σ τ where
  series := fun _ => 0
  constantCoeff_eq_zero := fun _ => constantCoeff_zero

/-- Composition, with the map applied first on the right. -/
def comp [Finite τ] (g : CoordinateMap R τ υ) (f : CoordinateMap R σ τ) :
    CoordinateMap R σ υ where
  series i := subst f.series (g.series i)
  constantCoeff_eq_zero i :=
    constantCoeff_subst_eq_zero f.hasSubst f.constantCoeff_eq_zero
      (g.constantCoeff_eq_zero i)

@[simp]
theorem id_series (i : σ) : (id (R := R) (σ := σ)).series i = X i := rfl

@[simp]
theorem zero_series (i : τ) : (zero (R := R) (σ := σ)).series i = 0 := rfl

@[simp]
theorem comp_series [Finite τ] (g : CoordinateMap R τ υ) (f : CoordinateMap R σ τ) (i : υ) :
    (g.comp f).series i = subst f.series (g.series i) := rfl

@[simp]
theorem comp_id [Finite σ] (f : CoordinateMap R σ τ) : f.comp id = f := by
  apply CoordinateMap.ext
  funext i
  exact congrFun (subst_self (R := R)) (f.series i)

@[simp]
theorem id_comp [Finite τ] (f : CoordinateMap R σ τ) : id.comp f = f := by
  apply CoordinateMap.ext
  funext i
  exact subst_X f.hasSubst i

theorem comp_assoc [Finite τ] [Finite υ] (h : CoordinateMap R υ ω) (g : CoordinateMap R τ υ)
    (f : CoordinateMap R σ τ) : (h.comp g).comp f = h.comp (g.comp f) := by
  apply CoordinateMap.ext
  funext i
  exact subst_comp_subst_apply g.hasSubst f.hasSubst (h.series i)

@[simp]
theorem zero_comp [Finite τ] (f : CoordinateMap R σ τ) :
    (zero (R := R) (τ := υ)).comp f = zero := by
  apply CoordinateMap.ext
  funext i
  change subst f.series 0 = 0
  rw [← substAlgHom_apply f.hasSubst, map_zero]

@[simp]
theorem comp_zero [Finite σ] (f : CoordinateMap R σ τ) :
    f.comp (zero (σ := υ)) = zero := by
  apply CoordinateMap.ext
  funext i
  exact subst_zero_of_constantCoeff_zero (f.constantCoeff_eq_zero i)

/-- A tuple of selected coordinate variables; it includes projections and
coordinate permutations. -/
def vars (a : τ → σ) : CoordinateMap R σ τ where
  series i := X (a i)
  constantCoeff_eq_zero _ := constantCoeff_X _

/-- Pair two maps with the same source. -/
def pair (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ) :
    CoordinateMap R σ (τ ⊕ υ) where
  series := Sum.elim f.series g.series
  constantCoeff_eq_zero := Sum.rec f.constantCoeff_eq_zero g.constantCoeff_eq_zero

/-- First projection. -/
def fst : CoordinateMap R (σ ⊕ τ) σ := vars Sum.inl

/-- Second projection. -/
def snd : CoordinateMap R (σ ⊕ τ) τ := vars Sum.inr

@[simp]
theorem vars_series (a : τ → σ) (i : τ) :
    (vars (R := R) a).series i = X (a i) := rfl

@[simp]
theorem pair_series_inl (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ) (i : τ) :
    (f.pair g).series (Sum.inl i) = f.series i := rfl

@[simp]
theorem pair_series_inr (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ) (i : υ) :
    (f.pair g).series (Sum.inr i) = g.series i := rfl

@[simp]
theorem pair_comp [Finite τ] (f : CoordinateMap R τ υ) (g : CoordinateMap R τ ω)
    (h : CoordinateMap R σ τ) : (f.pair g).comp h = (f.comp h).pair (g.comp h) := by
  apply CoordinateMap.ext
  funext i
  cases i <;> rfl

@[simp]
theorem fst_pair [Finite τ] [Finite υ] (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ) :
    fst.comp (f.pair g) = f := by
  apply CoordinateMap.ext
  funext i
  exact subst_X (f.pair g).hasSubst (Sum.inl i)

@[simp]
theorem snd_pair [Finite τ] [Finite υ] (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ) :
    snd.comp (f.pair g) = g := by
  apply CoordinateMap.ext
  funext i
  exact subst_X (f.pair g).hasSubst (Sum.inr i)

@[simp]
theorem pair_fst_snd :
    (fst (R := R) (σ := σ) (τ := τ)).pair snd = id := by
  apply CoordinateMap.ext
  funext i
  cases i <;> rfl

end CoordinateMap

/-- Substitutable tuples of power series. For a finite coordinate set, this
is exactly the condition that each constant coefficient be nilpotent. -/
def SeriesPoint (R : Type u) [CommRing R] (σ κ : Type) :=
  {x : σ → MvPowerSeries κ R // HasSubst x}

namespace SeriesPoint

@[ext]
theorem ext {x y : SeriesPoint R σ κ} (h : ∀ i, x.val i = y.val i) : x = y :=
  Subtype.ext (funext h)

/-- The zero tuple. -/
def zero : SeriesPoint R σ κ := ⟨fun _ => 0, HasSubst.zero⟩

/-- Concatenate two substitutable tuples. -/
def pair [Finite σ] [Finite τ] (x : SeriesPoint R σ κ) (y : SeriesPoint R τ κ) :
    SeriesPoint R (σ ⊕ τ) κ :=
  ⟨Sum.elim x.val y.val, hasSubst_of_constantCoeff_nilpotent
    (Sum.rec x.property.const_coeff y.property.const_coeff)⟩

/-- Evaluate a pointed formal map at a substitutable tuple. -/
def eval [Finite τ] (f : CoordinateMap R σ τ) (x : SeriesPoint R σ κ) :
    SeriesPoint R τ κ :=
  ⟨fun i => subst x.val (f.series i), by
    simpa only [substAlgHom_apply] using f.hasSubst.comp x.property⟩

@[simp]
theorem zero_val (i : σ) : (zero (R := R) (κ := κ)).val i = 0 := rfl

@[simp]
theorem pair_val_inl [Finite σ] [Finite τ] (x : SeriesPoint R σ κ) (y : SeriesPoint R τ κ) (i : σ) :
    (x.pair y).val (Sum.inl i) = x.val i := rfl

@[simp]
theorem pair_val_inr [Finite σ] [Finite τ] (x : SeriesPoint R σ κ) (y : SeriesPoint R τ κ) (i : τ) :
    (x.pair y).val (Sum.inr i) = y.val i := rfl

@[simp]
theorem eval_val [Finite τ] (f : CoordinateMap R σ τ) (x : SeriesPoint R σ κ) (i : τ) :
    (eval f x).val i = subst x.val (f.series i) := rfl

@[simp]
theorem eval_id [Finite σ] (x : SeriesPoint R σ κ) : eval CoordinateMap.id x = x := by
  apply SeriesPoint.ext
  intro i
  exact subst_X x.property i

@[simp]
theorem eval_zero [Finite τ] (x : SeriesPoint R σ κ) :
    eval (CoordinateMap.zero (τ := τ)) x = zero := by
  apply SeriesPoint.ext
  intro i
  change subst x.val 0 = 0
  rw [← substAlgHom_apply x.property, map_zero]

@[simp]
theorem eval_at_zero [Finite τ] (f : CoordinateMap R σ τ) :
    eval f (zero (κ := κ)) = zero := by
  apply SeriesPoint.ext
  intro i
  exact subst_zero_of_constantCoeff_zero (f.constantCoeff_eq_zero i)

theorem eval_comp [Finite τ] [Finite υ] (g : CoordinateMap R τ υ) (f : CoordinateMap R σ τ)
    (x : SeriesPoint R σ κ) : eval (g.comp f) x = eval g (eval f x) := by
  apply SeriesPoint.ext
  intro i
  exact subst_comp_subst_apply f.hasSubst x.property (g.series i)

@[simp]
theorem eval_pair [Finite τ] [Finite υ] (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ)
    (x : SeriesPoint R σ κ) : eval (f.pair g) x = (eval f x).pair (eval g x) := by
  apply SeriesPoint.ext
  intro i
  cases i <;> rfl

@[simp]
theorem eval_fst [Finite σ] [Finite τ] (x : SeriesPoint R σ κ) (y : SeriesPoint R τ κ) :
    eval CoordinateMap.fst (x.pair y) = x := by
  apply SeriesPoint.ext
  intro i
  exact subst_X (x.pair y).property (Sum.inl i)

@[simp]
theorem eval_snd [Finite σ] [Finite τ] (x : SeriesPoint R σ κ) (y : SeriesPoint R τ κ) :
    eval CoordinateMap.snd (x.pair y) = y := by
  apply SeriesPoint.ext
  intro i
  exact subst_X (x.pair y).property (Sum.inr i)

/-- Nilpotent tuples are the points obtained by taking no formal variables. -/
def nilpotentEquiv [Finite σ] :
    SeriesPoint R σ Empty ≃ {x : σ → R // ∀ i, IsNilpotent (x i)} where
  toFun x := ⟨fun i => (x.val i).constantCoeff, x.property.const_coeff⟩
  invFun x := ⟨fun i => C (x.val i), hasSubst_of_constantCoeff_nilpotent
    (fun i => by simpa using x.property i)⟩
  left_inv x := by
    apply SeriesPoint.ext
    intro i
    exact (MvPowerSeries.isEmptyEquiv Empty R).symm_apply_apply (x.val i)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact constantCoeff_C _

end SeriesPoint

end Langlands.FormalGroup
