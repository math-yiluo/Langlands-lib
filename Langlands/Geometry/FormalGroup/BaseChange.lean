import Langlands.Geometry.FormalGroup.Morphism
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-! # Change of coefficient ring for formal group laws -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

open MvPowerSeries

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable {T : Type w} [CommRing T]
variable {σ τ υ κ : Type}

namespace CoordinateMap

/-- Apply a ring homomorphism to every power-series coefficient. -/
def map (φ : R →+* S) (f : CoordinateMap R σ τ) : CoordinateMap S σ τ where
  series i := (f.series i).map φ
  constantCoeff_eq_zero i := by simp [constantCoeff_map, f.constantCoeff_eq_zero i]

@[simp]
theorem map_series (φ : R →+* S) (f : CoordinateMap R σ τ) (i : τ) :
    (f.map φ).series i = (f.series i).map φ := rfl

@[simp]
theorem map_id (φ : R →+* S) : (id (R := R) (σ := σ)).map φ = id := by
  apply CoordinateMap.ext
  funext i
  exact map_X φ i

@[simp]
theorem map_zero (φ : R →+* S) : (zero (R := R) (σ := σ) (τ := τ)).map φ = zero := by
  apply CoordinateMap.ext
  funext i
  exact _root_.map_zero _

@[simp]
theorem map_vars (φ : R →+* S) (a : τ → σ) : (vars a).map φ = vars a := by
  apply CoordinateMap.ext
  funext i
  exact map_X φ (a i)

@[simp]
theorem map_pair (φ : R →+* S) (f : CoordinateMap R σ τ) (g : CoordinateMap R σ υ) :
    (f.pair g).map φ = (f.map φ).pair (g.map φ) := by
  apply CoordinateMap.ext
  funext i
  cases i <;> rfl

@[simp]
theorem map_comp [Finite τ] (φ : R →+* S)
    (g : CoordinateMap R τ υ) (f : CoordinateMap R σ τ) :
    (g.comp f).map φ = (g.map φ).comp (f.map φ) := by
  apply CoordinateMap.ext
  funext i
  exact map_subst f.hasSubst (g.series i)

@[simp]
theorem map_fst (φ : R →+* S) : (fst (R := R) (σ := σ) (τ := τ)).map φ = fst :=
  map_vars φ _

@[simp]
theorem map_snd (φ : R →+* S) : (snd (R := R) (σ := σ) (τ := τ)).map φ = snd :=
  map_vars φ _

@[simp]
theorem map_ringHom_id (f : CoordinateMap R σ τ) : f.map (RingHom.id R) = f := by
  apply CoordinateMap.ext
  funext i
  change MvPowerSeries.map (RingHom.id R) _ = _
  rw [MvPowerSeries.map_id]
  rfl

@[simp]
theorem map_ringHom_comp (φ : R →+* S) (ψ : S →+* T) (f : CoordinateMap R σ τ) :
    (f.map φ).map ψ = f.map (ψ.comp φ) := by
  apply CoordinateMap.ext
  funext i
  exact MvPowerSeries.map_map _ _ _

end CoordinateMap

namespace SeriesPoint

/-- Change the coefficient ring in a series-valued point. -/
def map (φ : R →+* S) (x : SeriesPoint R σ κ) : SeriesPoint S σ κ :=
  ⟨fun i => (x.val i).map φ, x.property.map φ⟩

@[simp]
theorem map_val (φ : R →+* S) (x : SeriesPoint R σ κ) (i : σ) :
    (x.map φ).val i = (x.val i).map φ := rfl

@[simp]
theorem map_zero (φ : R →+* S) : (zero (R := R) (σ := σ) (κ := κ)).map φ = zero := by
  apply SeriesPoint.ext
  intro i
  exact _root_.map_zero _

@[simp]
theorem map_pair [Finite σ] [Finite τ] (φ : R →+* S)
    (x : SeriesPoint R σ κ) (y : SeriesPoint R τ κ) :
    (x.pair y).map φ = (x.map φ).pair (y.map φ) := by
  apply SeriesPoint.ext
  intro i
  cases i <;> rfl

@[simp]
theorem map_eval [Finite τ] (φ : R →+* S)
    (f : CoordinateMap R σ τ) (x : SeriesPoint R σ κ) :
    (eval f x).map φ = eval (f.map φ) (x.map φ) := by
  apply SeriesPoint.ext
  intro i
  exact map_subst x.property (f.series i)

@[simp]
theorem map_id (x : SeriesPoint R σ κ) : x.map (RingHom.id R) = x := by
  apply SeriesPoint.ext
  intro i
  change MvPowerSeries.map (RingHom.id R) _ = _
  rw [MvPowerSeries.map_id]
  rfl

@[simp]
theorem map_comp (φ : R →+* S) (ψ : S →+* T) (x : SeriesPoint R σ κ) :
    (x.map φ).map ψ = x.map (ψ.comp φ) := by
  apply SeriesPoint.ext
  intro i
  exact MvPowerSeries.map_map _ _ _

end SeriesPoint

namespace CommLaw

variable [Finite σ] [Finite τ]

/-- Scalar extension of a formal group law along a ring homomorphism. -/
def map (G : CommLaw R σ) (φ : R →+* S) : CommLaw S σ where
  addition := G.addition.map φ
  inverse := G.inverse.map φ
  zero_add := by
    have h := congrArg (CoordinateMap.map φ) G.zero_add
    simpa only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_zero,
      CoordinateMap.map_id] using h
  add_zero := by
    have h := congrArg (CoordinateMap.map φ) G.add_zero
    simpa only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_zero,
      CoordinateMap.map_id] using h
  add_assoc := by
    have h := congrArg (CoordinateMap.map φ) G.add_assoc
    simpa only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_fst,
      CoordinateMap.map_snd] using h
  add_comm := by
    have h := congrArg (CoordinateMap.map φ) G.add_comm
    simpa only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_fst,
      CoordinateMap.map_snd] using h
  neg_add := by
    have h := congrArg (CoordinateMap.map φ) G.neg_add
    simpa only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_zero,
      CoordinateMap.map_id] using h

/-- Coefficient change induces an additive map on series-valued points. -/
def mapPoints (G : CommLaw R σ) (φ : R →+* S) : G.Point κ →+ (G.map φ).Point κ where
  toFun := SeriesPoint.map φ
  map_zero' := SeriesPoint.map_zero φ
  map_add' x y := by
    change SeriesPoint R σ κ at x y
    change (SeriesPoint.eval G.addition (x.pair y)).map φ =
      SeriesPoint.eval (G.addition.map φ) ((x.map φ).pair (y.map φ))
    rw [SeriesPoint.map_eval, SeriesPoint.map_pair]

/-- Base change of a formal homomorphism. -/
def Hom.map {G : CommLaw R σ} {H : CommLaw R τ} (f : Hom G H) (φ : R →+* S) :
    Hom (G.map φ) (H.map φ) where
  toCoordinateMap := f.toCoordinateMap.map φ
  map_add := by
    have h := congrArg (CoordinateMap.map φ) f.map_add
    simp only [CoordinateMap.map_comp, CoordinateMap.map_pair, CoordinateMap.map_fst,
      CoordinateMap.map_snd] at h
    exact h

/-- Points over a coefficient algebra are nilpotent tuples with the base-changed law. -/
def AlgebraPoint (G : CommLaw R σ) (A : Type v) [CommRing A] [Algebra R A] :=
  (G.map (algebraMap R A)).Point Empty

instance (G : CommLaw R σ) (A : Type v) [CommRing A] [Algebra R A] :
    AddCommGroup (G.AlgebraPoint A) :=
  inferInstanceAs (AddCommGroup ((G.map (algebraMap R A)).Point Empty))

/-- The underlying points are exactly the nilpotent coordinate tuples. -/
def algebraPointEquiv (G : CommLaw R σ) (A : Type v) [CommRing A] [Algebra R A] :
    G.AlgebraPoint A ≃ {x : σ → A // ∀ i, IsNilpotent (x i)} :=
  SeriesPoint.nilpotentEquiv

variable {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]
variable {C : Type v} [CommRing C] [Algebra R C]

/-- Functoriality of nilpotent points in the coefficient algebra. -/
def algebraMapPoints (G : CommLaw R σ) (f : A →ₐ[R] B) :
    G.AlgebraPoint A →+ G.AlgebraPoint B where
  toFun := SeriesPoint.map f.toRingHom
  map_zero' := SeriesPoint.map_zero f.toRingHom
  map_add' x y := by
    change SeriesPoint A σ Empty at x y
    change (SeriesPoint.eval (G.addition.map (algebraMap R A)) (x.pair y)).map
      f.toRingHom = SeriesPoint.eval (G.addition.map (algebraMap R B))
        ((x.map f.toRingHom).pair (y.map f.toRingHom))
    rw [SeriesPoint.map_eval, SeriesPoint.map_pair, CoordinateMap.map_ringHom_comp]
    have h : f.toRingHom.comp (algebraMap R A) = algebraMap R B :=
      RingHom.ext f.commutes
    rw [h]

@[simp]
theorem algebraMapPoints_id (G : CommLaw R σ) (x : G.AlgebraPoint A) :
    G.algebraMapPoints (AlgHom.id R A) x = x := by
  change SeriesPoint A σ Empty at x
  exact SeriesPoint.map_id x

@[simp]
theorem algebraMapPoints_comp (G : CommLaw R σ) (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (x : G.AlgebraPoint A) :
    G.algebraMapPoints (g.comp f) x = G.algebraMapPoints g (G.algebraMapPoints f x) := by
  change SeriesPoint A σ Empty at x
  exact (SeriesPoint.map_comp f.toRingHom g.toRingHom x).symm

open CategoryTheory

/-- The formal group law as an actual group-valued functor on coefficient algebras. -/
def algebraPointFunctor (G : CommLaw R σ) : CommAlgCat.{v} R ⥤ AddCommGrpCat.{v} where
  obj A := AddCommGrpCat.of (G.AlgebraPoint A)
  map f := AddCommGrpCat.ofHom (G.algebraMapPoints f.hom)
  map_id A := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact G.algebraMapPoints_id x
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact G.algebraMapPoints_comp f.hom g.hom x

end CommLaw

end Langlands.FormalGroup
