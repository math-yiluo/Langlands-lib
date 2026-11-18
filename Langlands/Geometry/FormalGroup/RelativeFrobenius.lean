import Langlands.Geometry.FormalGroup.OrderAction
import Mathlib.RingTheory.MvPowerSeries.Expand

/-! # Actual relative Frobenius maps of formal groups and formal order modules -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

open MvPowerSeries

variable {R : Type u} [CommRing R] (p n : ℕ) [ExpChar R p]
variable {σ τ : Type} [Finite σ] [Finite τ]

namespace CoordinateMap

/-- The actual relative Frobenius coordinate map raises every formal variable to `p^n`. -/
def frobeniusPow : CoordinateMap R σ σ where
  series i := X i ^ (p ^ n)
  constantCoeff_eq_zero i := by
    rw [map_pow, constantCoeff_X, zero_pow (pow_ne_zero n (expChar_ne_zero R p))]

omit [Finite σ] in
@[simp]
theorem frobeniusPow_series (i : σ) :
    (frobeniusPow (R := R) (σ := σ) p n).series i = X i ^ (p ^ n) := rfl

omit [Finite σ] in
/-- The zeroth actual Frobenius iterate is the identity formal map. -/
@[simp]
theorem frobeniusPow_zero :
    frobeniusPow (R := R) (σ := σ) p 0 = id := by
  apply CoordinateMap.ext
  funext i
  simp only [frobeniusPow_series, pow_zero, pow_one, id_series]

/-- Addition of Frobenius exponents is actual formal composition. -/
theorem frobeniusPow_add (m : ℕ) :
    frobeniusPow (R := R) (σ := σ) p (n + m) =
      (frobeniusPow p m).comp (frobeniusPow p n) := by
  apply CoordinateMap.ext
  funext i
  change X i ^ (p ^ (n + m)) =
    subst (frobeniusPow (R := R) (σ := σ) p n).series (X i ^ (p ^ m))
  rw [subst_pow (frobeniusPow p n).hasSubst, subst_X (frobeniusPow p n).hasSubst]
  change X i ^ (p ^ (n + m)) = (X i ^ (p ^ n)) ^ (p ^ m)
  rw [← pow_mul, pow_add]

/-- Relative Frobenius commutes with every actual formal coordinate map after coefficient Frobenius. -/
theorem frobeniusPow_natural (f : CoordinateMap R σ τ) :
    (frobeniusPow p n).comp f =
      (f.map (iterateFrobenius R p n)).comp (frobeniusPow p n) := by
  apply CoordinateMap.ext
  funext i
  change subst f.series (X i ^ (p ^ n)) =
    subst (fun j => X j ^ (p ^ n)) ((f.series i).map (iterateFrobenius R p n))
  rw [subst_pow f.hasSubst, subst_X f.hasSubst]
  symm
  have hr := map_iterateFrobenius_expand p (expChar_ne_zero R p) (f.series i) n
  rw [MvPowerSeries.map_expand] at hr
  simpa only [MvPowerSeries.expand, substAlgHom_apply] using hr

/-- The actual power map on a sum of coordinate sets is the pair of the two projected power maps. -/
theorem frobeniusPow_pair :
    ((frobeniusPow (R := R) (σ := σ) p n).comp fst).pair
      ((frobeniusPow (σ := τ) p n).comp snd) = frobeniusPow (σ := σ ⊕ τ) p n := by
  apply CoordinateMap.ext
  funext i
  cases i <;>
    simp only [pair_series_inl, pair_series_inr, comp_series, frobeniusPow_series,
      subst_pow (fst (R := R) (σ := σ) (τ := τ)).hasSubst,
      subst_pow (snd (R := R) (σ := σ) (τ := τ)).hasSubst,
      subst_X (fst (R := R) (σ := σ) (τ := τ)).hasSubst,
      subst_X (snd (R := R) (σ := σ) (τ := τ)).hasSubst]
  all_goals rfl

omit [Finite σ] in
/-- Frobenius on formal variables is unchanged by arbitrary coefficient extension. -/
theorem map_frobeniusPow {S : Type v} [CommRing S] [ExpChar S p] (f : R →+* S) :
    (frobeniusPow (R := R) (σ := σ) p n).map f = frobeniusPow (R := S) p n := by
  apply CoordinateMap.ext
  funext i
  simp only [map_series, frobeniusPow_series, map_pow, MvPowerSeries.map_X]

/-- Evaluation of the actual Frobenius formal map raises each original series coordinate to `p^n`. -/
theorem eval_frobeniusPow {κ : Type} (x : SeriesPoint R σ κ) (i : σ) :
    (SeriesPoint.eval (frobeniusPow p n) x).val i = x.val i ^ (p ^ n) := by
  exact (subst_pow x.property (X i) (p ^ n)).trans
    (congrArg (fun a => a ^ (p ^ n)) (subst_X x.property i))

end CoordinateMap

namespace CommLaw

/-- The actual relative Frobenius is an actual homomorphism to the coefficient-Frobenius twist. -/
def frobeniusHom (G : CommLaw R σ) (φ : R →+* R) (hφ : φ = iterateFrobenius R p n) :
    Hom G (G.map φ) where
  toCoordinateMap := CoordinateMap.frobeniusPow p n
  map_add := by
    change (CoordinateMap.frobeniusPow p n).comp G.addition =
      (G.addition.map φ).comp
        (((CoordinateMap.frobeniusPow p n).comp CoordinateMap.fst).pair
          ((CoordinateMap.frobeniusPow p n).comp CoordinateMap.snd))
    rw [CoordinateMap.frobeniusPow_pair, hφ]
    exact CoordinateMap.frobeniusPow_natural p n G.addition

end CommLaw

namespace ModuleLaw

variable {O : Type v} [CommRing O] [Algebra O R]

/-- An actual scalar-algebra Frobenius map gives an actual O-linear relative Frobenius formal map. -/
def frobeniusHom (M : ModuleLaw O R σ) (θ : R →ₐ[O] R)
    (hθ : θ.toRingHom = iterateFrobenius R p n) : Hom M (M.map θ) where
  toHom := M.groupLaw.frobeniusHom p n θ.toRingHom hθ
  commutes a := by
    apply CommLaw.Hom.ext
    change (CoordinateMap.frobeniusPow p n).comp (M.action a).toCoordinateMap =
      ((M.action a).toCoordinateMap.map θ.toRingHom).comp (CoordinateMap.frobeniusPow p n)
    rw [hθ]
    exact CoordinateMap.frobeniusPow_natural p n _

namespace OrderAction

variable {D : Type w} [Ring D] [Algebra O D] {M : ModuleLaw O R σ}

/-- Relative Frobenius commutes with every element of the actual full acting order. -/
def frobeniusHom (E : OrderAction D M) (θ : R →ₐ[O] R)
    (hθ : θ.toRingHom = iterateFrobenius R p n) : Hom E (E.map θ) :=
  ⟨M.frobeniusHom p n θ hθ, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.frobeniusPow p n).comp (E.action d).toHom.toCoordinateMap =
      ((E.action d).toHom.toCoordinateMap.map θ.toRingHom).comp (CoordinateMap.frobeniusPow p n)
    rw [hθ]
    exact CoordinateMap.frobeniusPow_natural p n _⟩

/-- The full-order relative Frobenius retains exactly the original formal variable-power series. -/
@[simp]
theorem frobeniusHom_coordinates (E : OrderAction D M) (θ : R →ₐ[O] R)
    (hθ : θ.toRingHom = iterateFrobenius R p n) :
    (E.frobeniusHom p n θ hθ).val.toHom.toCoordinateMap = CoordinateMap.frobeniusPow p n := rfl

end OrderAction
end ModuleLaw

end Langlands.FormalGroup
