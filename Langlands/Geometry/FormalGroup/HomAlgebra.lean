import Langlands.Geometry.FormalGroup.BaseChange
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Defs

/-! # Addition of formal homomorphisms and the formal endomorphism ring -/

noncomputable section

universe u v

namespace Langlands.FormalGroup

open CoordinateMap

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S]
variable {σ τ υ κ : Type} [Finite σ] [Finite τ] [Finite υ]

namespace CoordinateMap

/-- Evaluation at the tuple of variables detects equality of pointed maps. -/
theorem ext_eval {f g : CoordinateMap R σ τ}
    (h : ∀ x : SeriesPoint R σ σ, SeriesPoint.eval f x = SeriesPoint.eval g x) : f = g := by
  apply CoordinateMap.ext
  funext i
  have e := congrArg (fun x : SeriesPoint R τ σ => x.val i)
    (h ⟨MvPowerSeries.X, (CoordinateMap.id (R := R) (σ := σ)).hasSubst⟩)
  change MvPowerSeries.subst MvPowerSeries.X (f.series i) =
    MvPowerSeries.subst MvPowerSeries.X (g.series i) at e
  rw [MvPowerSeries.subst_self] at e
  exact e

end CoordinateMap

namespace CommLaw

variable {G : CommLaw R σ} {H : CommLaw R τ} {I : CommLaw R υ}

/-- Evaluate a pointed map with both group laws recorded in its type. -/
def evalCoordinateMap (G : CommLaw R σ) (H : CommLaw R τ) (f : CoordinateMap R σ τ)
    (x : G.Point κ) : H.Point κ := SeriesPoint.eval f x

@[simp]
theorem evalCoordinateMap_zero (x : G.Point κ) :
    G.evalCoordinateMap H zero x = 0 := SeriesPoint.eval_zero x

theorem evalCoordinateMap_addMaps (f g : CoordinateMap R σ τ) (x : G.Point κ) :
    G.evalCoordinateMap H (H.addition.comp (f.pair g)) x =
      G.evalCoordinateMap H f x + G.evalCoordinateMap H g x :=
  (SeriesPoint.eval_comp _ _ x).trans
    (congrArg (SeriesPoint.eval H.addition) (SeriesPoint.eval_pair _ _ x))

theorem evalCoordinateMap_inverse (f : CoordinateMap R σ τ) (x : G.Point κ) :
    G.evalCoordinateMap H (H.inverse.comp f) x = -(G.evalCoordinateMap H f x) :=
  SeriesPoint.eval_comp _ _ x

namespace Hom

/-- Construct a formal homomorphism from additivity on every series-point group.
The generic tuple of variables recovers the formal-series identity. -/
def ofPointAdditive (f : CoordinateMap R σ τ)
    (h : ∀ (κ : Type) (x y : G.Point κ),
      G.evalCoordinateMap H f (x + y) =
        G.evalCoordinateMap H f x + G.evalCoordinateMap H f y) :
    Hom G H where
  toCoordinateMap := f
  map_add := by
    apply CoordinateMap.ext_eval
    intro z
    have hz : (SeriesPoint.eval fst z).pair (SeriesPoint.eval snd z) = z := by
      rw [← SeriesPoint.eval_pair, pair_fst_snd, SeriesPoint.eval_id]
    rw [← hz]
    simp only [SeriesPoint.eval_comp, SeriesPoint.eval_pair, SeriesPoint.eval_fst,
      SeriesPoint.eval_snd]
    exact h _ _ _

/-- Formal homomorphisms are determined by their maps on generic series points. -/
theorem ext_onPoints {f g : Hom G H}
    (h : ∀ x : G.Point σ, f.onPoints x = g.onPoints x) : f = g := by
  apply Hom.ext
  exact CoordinateMap.ext_eval h

/-- The zero formal homomorphism. -/
instance : Zero (Hom G H) :=
  ⟨ofPointAdditive zero (by
    intro κ x y
    simp only [evalCoordinateMap_zero, _root_.zero_add])⟩

/-- Add homomorphisms using the target's formal addition law. -/
instance : Add (Hom G H) :=
  ⟨fun f g => ofPointAdditive (H.addition.comp (f.toCoordinateMap.pair g.toCoordinateMap))
    (by
      intro κ x y
      rw [evalCoordinateMap_addMaps, evalCoordinateMap_addMaps, evalCoordinateMap_addMaps]
      change f.onPoints (x + y) + g.onPoints (x + y) =
        (f.onPoints x + g.onPoints x) + (f.onPoints y + g.onPoints y)
      rw [_root_.map_add, _root_.map_add]
      exact add_add_add_comm _ _ _ _)⟩

/-- Negate a homomorphism using the target's formal inverse series. -/
instance : Neg (Hom G H) :=
  ⟨fun f => ofPointAdditive (H.inverse.comp f.toCoordinateMap) (by
    intro κ x y
    rw [evalCoordinateMap_inverse, evalCoordinateMap_inverse, evalCoordinateMap_inverse]
    change -(f.onPoints (x + y)) = -(f.onPoints x) + -(f.onPoints y)
    rw [_root_.map_add, _root_.neg_add])⟩

@[simp]
theorem zero_toCoordinateMap : (0 : Hom G H).toCoordinateMap = zero := rfl

@[simp]
theorem add_toCoordinateMap (f g : Hom G H) :
    (f + g).toCoordinateMap = H.addition.comp (f.toCoordinateMap.pair g.toCoordinateMap) := rfl

@[simp]
theorem neg_toCoordinateMap (f : Hom G H) :
    (-f).toCoordinateMap = H.inverse.comp f.toCoordinateMap := rfl

@[simp]
theorem onPoints_zero (x : G.Point κ) : (0 : Hom G H).onPoints x = 0 :=
  SeriesPoint.eval_zero x

@[simp]
theorem onPoints_add (f g : Hom G H) (x : G.Point κ) :
    (f + g).onPoints x = f.onPoints x + g.onPoints x := by
  change SeriesPoint R σ κ at x
  exact (SeriesPoint.eval_comp _ _ x).trans
    (congrArg (SeriesPoint.eval H.addition) (SeriesPoint.eval_pair _ _ x))

@[simp]
theorem onPoints_neg (f : Hom G H) (x : G.Point κ) :
    (-f).onPoints x = -(f.onPoints x) := by
  change SeriesPoint R σ κ at x
  exact SeriesPoint.eval_comp _ _ x

instance : AddCommGroup (Hom G H) where
  add_assoc f g h := ext_onPoints (by intro x; simp only [onPoints_add, _root_.add_assoc])
  zero_add f := ext_onPoints (by intro x; simp only [onPoints_add, onPoints_zero, _root_.zero_add])
  add_zero f := ext_onPoints (by intro x; simp only [onPoints_add, onPoints_zero, _root_.add_zero])
  neg_add_cancel f := ext_onPoints (by
    intro x
    simp only [onPoints_add, onPoints_neg, onPoints_zero, neg_add_cancel])
  add_comm f g := ext_onPoints (by intro x; simp only [onPoints_add, _root_.add_comm])
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Evaluation is additive in the formal homomorphism. -/
def onPointsAddHom : Hom G H →+ (G.Point κ →+ H.Point κ) where
  toFun := onPoints
  map_zero' := by ext x; exact onPoints_zero x
  map_add' f g := by ext x; exact onPoints_add f g x

@[simp]
theorem comp_add (g : Hom H I) (f₁ f₂ : Hom G H) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_add, _root_.map_add]

@[simp]
theorem add_comp (g₁ g₂ : Hom H I) (f : Hom G H) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_add]

@[simp]
theorem comp_zero (g : Hom H I) : g.comp (0 : Hom G H) = 0 := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_zero, _root_.map_zero]

@[simp]
theorem zero_comp (f : Hom G H) : (0 : Hom H I).comp f = 0 := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_zero]

/-- Formal endomorphisms form a ring, with multiplication given by composition. -/
instance : Ring (Hom G G) where
  mul := comp
  one := id G
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

@[simp]
theorem map_zero (φ : R →+* S) :
    (0 : Hom G H).map φ = 0 := by
  apply Hom.ext
  exact CoordinateMap.map_zero φ

@[simp]
theorem map_add_hom (φ : R →+* S) (f g : Hom G H) :
    (f + g).map φ = f.map φ + g.map φ := by
  apply Hom.ext
  exact (CoordinateMap.map_comp φ H.addition (f.toCoordinateMap.pair g.toCoordinateMap)).trans
    (congrArg (fun x => (H.addition.map φ).comp x)
      (CoordinateMap.map_pair φ f.toCoordinateMap g.toCoordinateMap))

@[simp]
theorem map_id (φ : R →+* S) :
    (id G).map φ = id (G.map φ) := by
  apply Hom.ext
  exact CoordinateMap.map_id φ

@[simp]
theorem map_comp (φ : R →+* S) (g : Hom H I) (f : Hom G H) :
    (g.comp f).map φ = (g.map φ).comp (f.map φ) := by
  apply Hom.ext
  exact CoordinateMap.map_comp φ g.toCoordinateMap f.toCoordinateMap

/-- Coefficient change acts by a ring homomorphism on formal endomorphisms. -/
def mapEnd (G : CommLaw R σ) (φ : R →+* S) :
    Hom G G →+* Hom (G.map φ) (G.map φ) where
  toFun f := f.map φ
  map_zero' := map_zero φ
  map_add' := map_add_hom φ
  map_one' := map_id φ
  map_mul' := map_comp φ

end Hom

end CommLaw

end Langlands.FormalGroup
