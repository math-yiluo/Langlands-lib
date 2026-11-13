import Langlands.Geometry.FormalGroup.Coordinates
import Mathlib.Algebra.Group.Defs

/-!
# Finite-dimensional commutative formal group laws

Group objects in pointed finite formal coordinates and their series points.
Inverses are included as part of the formal-coordinate data.
-/

noncomputable section

universe u

namespace Langlands.FormalGroup

open CoordinateMap

variable {R : Type u} [CommRing R]
variable {σ τ υ κ : Type} [Finite σ] [Finite τ] [Finite υ]

/-- A commutative formal group law in finitely many coordinates. The axioms
are equalities of pointed power-series maps. -/
structure CommLaw (R : Type u) [CommRing R] (σ : Type) [Finite σ] where
  addition : CoordinateMap R (σ ⊕ σ) σ
  inverse : CoordinateMap R σ σ
  zero_add : addition.comp (zero.pair CoordinateMap.id) = CoordinateMap.id
  add_zero : addition.comp (CoordinateMap.id.pair zero) = CoordinateMap.id
  add_assoc : addition.comp ((addition.comp fst).pair snd) =
    addition.comp ((fst.comp fst).pair (addition.comp ((snd.comp fst).pair snd)))
  add_comm : addition.comp (snd.pair fst) = addition
  neg_add : addition.comp (inverse.pair CoordinateMap.id) = zero

namespace CommLaw

/-- Series-valued points, indexed by the law that supplies their group structure. -/
@[nolint unusedArguments]
def Point (_G : CommLaw R σ) (κ : Type) := SeriesPoint R σ κ

variable (G : CommLaw R σ)

instance : Zero (G.Point κ) := ⟨SeriesPoint.zero⟩

instance : Add (G.Point κ) :=
  ⟨fun x y => SeriesPoint.eval G.addition (x.pair y)⟩

instance : Neg (G.Point κ) := ⟨fun x => SeriesPoint.eval G.inverse x⟩

@[simp]
theorem zero_add_point (x : G.Point κ) : 0 + x = x := by
  change SeriesPoint R σ κ at x
  have h := congrArg (fun f => SeriesPoint.eval f x) G.zero_add
  rw [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_zero,
    SeriesPoint.eval_id] at h
  exact h

@[simp]
theorem add_zero_point (x : G.Point κ) : x + 0 = x := by
  change SeriesPoint R σ κ at x
  have h := congrArg (fun f => SeriesPoint.eval f x) G.add_zero
  simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_zero,
    SeriesPoint.eval_id] at h
  exact h

theorem add_assoc_point (x y z : G.Point κ) : (x + y) + z = x + (y + z) := by
  change SeriesPoint R σ κ at x y z
  have h := congrArg (fun f => SeriesPoint.eval f ((x.pair y).pair z)) G.add_assoc
  simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_fst,
    SeriesPoint.eval_snd] at h
  exact h

theorem add_comm_point (x y : G.Point κ) : x + y = y + x := by
  change SeriesPoint R σ κ at x y
  have h := congrArg (fun f => SeriesPoint.eval f (x.pair y)) G.add_comm
  simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair,
    SeriesPoint.eval_fst, SeriesPoint.eval_snd] at h
  exact h.symm

@[simp]
theorem neg_add_point (x : G.Point κ) : -x + x = 0 := by
  change SeriesPoint R σ κ at x
  have h := congrArg (fun f => SeriesPoint.eval f x) G.neg_add
  simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_id,
    SeriesPoint.eval_zero] at h
  exact h

instance : AddCommGroup (G.Point κ) where
  add_assoc := G.add_assoc_point
  zero_add := G.zero_add_point
  add_zero := G.add_zero_point
  neg_add_cancel := G.neg_add_point
  add_comm := G.add_comm_point
  nsmul := nsmulRec
  zsmul := zsmulRec

end CommLaw

end Langlands.FormalGroup
