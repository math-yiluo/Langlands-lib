import Langlands.Geometry.FormalGroup.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-! # Homomorphisms of commutative formal group laws -/

noncomputable section

universe u

namespace Langlands.FormalGroup

open CoordinateMap

variable {R : Type u} [CommRing R]
variable {σ τ υ ω κ : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]

namespace CommLaw

/-- A formal group homomorphism is a pointed formal map preserving addition. -/
@[ext]
structure Hom (G : CommLaw R σ) (H : CommLaw R τ) where
  toCoordinateMap : CoordinateMap R σ τ
  map_add : toCoordinateMap.comp G.addition =
    H.addition.comp ((toCoordinateMap.comp fst).pair (toCoordinateMap.comp snd))

namespace Hom

variable {G : CommLaw R σ} {H : CommLaw R τ} {I : CommLaw R υ} {J : CommLaw R ω}

/-- A formal homomorphism evaluates to an additive homomorphism on points. -/
def onPoints (f : Hom G H) : G.Point κ →+ H.Point κ where
  toFun := SeriesPoint.eval f.toCoordinateMap
  map_zero' := SeriesPoint.eval_at_zero f.toCoordinateMap
  map_add' x y := by
    change SeriesPoint R σ κ at x y
    have h := congrArg (fun m => SeriesPoint.eval m (x.pair y)) f.map_add
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair,
      SeriesPoint.eval_fst, SeriesPoint.eval_snd] at h
    exact h

@[simp]
theorem onPoints_apply (f : Hom G H) (x : G.Point κ) :
    f.onPoints x = SeriesPoint.eval f.toCoordinateMap x := rfl

/-- Identity homomorphism. -/
def id (G : CommLaw R σ) : Hom G G where
  toCoordinateMap := CoordinateMap.id
  map_add := by simp

/-- Composition, with the homomorphism applied first on the right. -/
def comp (g : Hom H I) (f : Hom G H) : Hom G I where
  toCoordinateMap := g.toCoordinateMap.comp f.toCoordinateMap
  map_add := by
    calc
      _ = g.toCoordinateMap.comp (f.toCoordinateMap.comp G.addition) := comp_assoc _ _ _
      _ = g.toCoordinateMap.comp
          (H.addition.comp ((f.toCoordinateMap.comp fst).pair
            (f.toCoordinateMap.comp snd))) := by rw [f.map_add]
      _ = (g.toCoordinateMap.comp H.addition).comp
          ((f.toCoordinateMap.comp fst).pair (f.toCoordinateMap.comp snd)) :=
        (comp_assoc _ _ _).symm
      _ = _ := by rw [g.map_add]; simp only [comp_assoc, pair_comp, fst_pair, snd_pair]

@[simp]
theorem id_toCoordinateMap : (id G).toCoordinateMap = CoordinateMap.id := rfl

@[simp]
theorem comp_toCoordinateMap (g : Hom H I) (f : Hom G H) :
    (g.comp f).toCoordinateMap = g.toCoordinateMap.comp f.toCoordinateMap := rfl

@[simp]
theorem comp_id (f : Hom G H) : f.comp (id G) = f := by
  apply Hom.ext
  exact CoordinateMap.comp_id _

@[simp]
theorem id_comp (f : Hom G H) : (id H).comp f = f := by
  apply Hom.ext
  exact CoordinateMap.id_comp _

theorem comp_assoc (h : Hom I J) (g : Hom H I) (f : Hom G H) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply Hom.ext
  exact CoordinateMap.comp_assoc _ _ _

@[simp]
theorem onPoints_id (x : G.Point κ) : (id G).onPoints x = x := by
  change SeriesPoint R σ κ at x
  exact SeriesPoint.eval_id x

@[simp]
theorem onPoints_comp (g : Hom H I) (f : Hom G H) (x : G.Point κ) :
    (g.comp f).onPoints x = g.onPoints (f.onPoints x) := by
  change SeriesPoint R σ κ at x
  exact SeriesPoint.eval_comp g.toCoordinateMap f.toCoordinateMap x

end Hom

/-- An isomorphism of formal group laws, with inverse formal homomorphism. -/
structure Iso (G : CommLaw R σ) (H : CommLaw R τ) where
  hom : Hom G H
  inv : Hom H G
  inv_hom : inv.comp hom = Hom.id G
  hom_inv : hom.comp inv = Hom.id H

namespace Iso

variable {G : CommLaw R σ} {H : CommLaw R τ}

/-- An isomorphism gives an additive equivalence on series-valued points. -/
def onPoints (f : Iso G H) : G.Point κ ≃+ H.Point κ where
  toFun := f.hom.onPoints
  invFun := f.inv.onPoints
  left_inv x := by
    rw [← Hom.onPoints_comp, f.inv_hom, Hom.onPoints_id]
  right_inv x := by
    rw [← Hom.onPoints_comp, f.hom_inv, Hom.onPoints_id]
  map_add' := f.hom.onPoints.map_add

end Iso

end CommLaw

end Langlands.FormalGroup
