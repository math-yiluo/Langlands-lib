import Langlands.Geometry.FormalGroup.CoordinateYoneda
import Langlands.Geometry.FormalGroup.NilpotentAlgebras

/-! # Formal module homomorphisms from natural maps of nilpotent points -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- Splitting a point of a pair of coordinate spaces into its two components. -/
theorem _root_.Langlands.FormalGroup.SeriesPoint.pair_eval_fst_snd {T : Type*} [CommRing T]
    {κ : Type} (z : SeriesPoint T (σ ⊕ τ) κ) :
    (SeriesPoint.eval CoordinateMap.fst z).pair (SeriesPoint.eval CoordinateMap.snd z) = z := by
  apply SeriesPoint.ext
  intro i
  cases i with
  | inl i => exact MvPowerSeries.subst_X z.property (Sum.inl i)
  | inr i => exact MvPowerSeries.subst_X z.property (Sum.inr i)

namespace Hom

/-- A formal O-module homomorphism is determined by its values on nilpotent
points over all coefficient algebras. -/
theorem ext_onAlgebraPoints {f g : Hom M N}
    (h : ∀ (T : CommAlgCat.{v} R) (x : M.AlgebraPoint T),
      f.onAlgebraPoints x = g.onAlgebraPoints x) : f = g := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  exact CoordinateMap.ext_of_eval fun T x => h T x

variable (Φ : ∀ T : CommAlgCat.{v} R, M.AlgebraPoint T → N.AlgebraPoint T)

/-- Naturality of a family of point maps in the coefficient algebra. -/
def IsNaturalOnPoints : Prop :=
  ∀ {T T' : CommAlgCat.{v} R} (ψ : T ⟶ T') (x : M.AlgebraPoint T),
    N.algebraMapPoints ψ.hom (Φ T x) = Φ T' (M.algebraMapPoints ψ.hom x)

variable {Φ}

theorem IsNaturalOnPoints.coordinate (hΦ : IsNaturalOnPoints Φ) :
    IsNaturalPointMap (R := R) (σ := σ) (τ := τ) Φ :=
  fun ψ x => hΦ ψ x

theorem zero_of_add
    (hadd : ∀ (T : CommAlgCat.{v} R) (x y : M.AlgebraPoint T), Φ T (x + y) = Φ T x + Φ T y)
    (T : CommAlgCat.{v} R) : Φ T SeriesPoint.zero = SeriesPoint.zero := by
  have h := hadd T 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

variable (Φ) in
/-- The formal O-module homomorphism attached to a natural family of additive,
O-linear maps on nilpotent points. -/
def ofNatural (hΦ : IsNaturalOnPoints Φ)
    (hadd : ∀ (T : CommAlgCat.{v} R) (x y : M.AlgebraPoint T), Φ T (x + y) = Φ T x + Φ T y)
    (hsmul : ∀ (T : CommAlgCat.{v} R) (a : O) (x : M.AlgebraPoint T), Φ T (a • x) = a • Φ T x) :
    Hom M N :=
  have h0 : ∀ T : CommAlgCat.{v} R, Φ T SeriesPoint.zero = SeriesPoint.zero := zero_of_add hadd
  let F : CoordinateMap R σ τ := CoordinateMap.ofNatural Φ hΦ.coordinate h0
  have hF : ∀ (T : CommAlgCat.{v} R) (x : SeriesPoint T σ Empty),
      SeriesPoint.eval (F.map (algebraMap R T)) x = Φ T x :=
    CoordinateMap.eval_ofNatural hΦ.coordinate h0
  { toHom :=
      { toCoordinateMap := F
        map_add := by
          apply CoordinateMap.ext_of_eval
          intro T z
          rw [CoordinateMap.map_comp, SeriesPoint.eval_comp, hF, CoordinateMap.map_comp,
            CoordinateMap.map_pair, CoordinateMap.map_comp, CoordinateMap.map_comp,
            CoordinateMap.map_fst, CoordinateMap.map_snd, SeriesPoint.eval_comp,
            SeriesPoint.eval_pair, SeriesPoint.eval_comp, SeriesPoint.eval_comp, hF, hF]
          rw [← SeriesPoint.pair_eval_fst_snd z]
          rw [SeriesPoint.eval_fst, SeriesPoint.eval_snd]
          exact hadd T (SeriesPoint.eval CoordinateMap.fst z)
            (SeriesPoint.eval CoordinateMap.snd z) }
    commutes := fun a => by
      apply CommLaw.Hom.ext
      apply CoordinateMap.ext_of_eval
      intro T x
      change SeriesPoint.eval ((F.comp (M.action a).toCoordinateMap).map (algebraMap R T)) x =
        SeriesPoint.eval (((N.action a).toCoordinateMap.comp F).map (algebraMap R T)) x
      rw [CoordinateMap.map_comp, CoordinateMap.map_comp, SeriesPoint.eval_comp,
        SeriesPoint.eval_comp, hF, hF]
      exact hsmul T a x }

theorem onAlgebraPoints_ofNatural (hΦ : IsNaturalOnPoints Φ)
    (hadd : ∀ (T : CommAlgCat.{v} R) (x y : M.AlgebraPoint T), Φ T (x + y) = Φ T x + Φ T y)
    (hsmul : ∀ (T : CommAlgCat.{v} R) (a : O) (x : M.AlgebraPoint T), Φ T (a • x) = a • Φ T x)
    (T : CommAlgCat.{v} R) (x : M.AlgebraPoint T) :
    (ofNatural Φ hΦ hadd hsmul).onAlgebraPoints x = Φ T x :=
  CoordinateMap.eval_ofNatural hΦ.coordinate (zero_of_add hadd) T x

end Hom

end Langlands.FormalGroup.ModuleLaw
