import Langlands.Geometry.FormalGroup.PointFactorization
import Langlands.Geometry.FormalGroup.IsogenyBaseChange
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Formal homomorphisms over nilpotent coefficient thickenings -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] {R S : Type v} [CommRing R] [CommRing S]
variable [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

/-- A single scalar power kills all points with a given coordinate nilpotence bound. -/
private theorem exists_smul_eq_zero_of_bounded_coords (hN : N.IsPiPowerTorsion π) (d : ℕ) :
    ∃ k : ℕ, ∀ (A : CommAlgCat.{v} R) (x : N.AlgebraPoint A),
      (∀ i, MvPowerSeries.constantCoeff (x.val i) ^ d = 0) → π ^ k • x = 0 := by
  let B : CommAlgCat.{v} R := CommAlgCat.of R (BoxAlgebra R τ d)
  let b : N.AlgebraPoint B := boxPoint R τ d
  obtain ⟨k, hk⟩ := hN B b
  refine ⟨k, fun A x hx => ?_⟩
  let β : B →ₐ[R] A := boxLift _ hx
  have hbx : N.algebraMapPoints β b = x :=
    boxPoint_map_boxLift x hx
  calc
    π ^ k • x = π ^ k • N.algebraMapPoints β b := congrArg (π ^ k • ·) hbx.symm
    _ = N.algebraMapPoints β (π ^ k • b) := ((N.algebraMapPoints β).map_smul _ _).symm
    _ = N.algebraMapPoints β 0 := congrArg (N.algebraMapPoints β) hk
    _ = 0 := (N.algebraMapPoints β).map_zero

private abbrev testIdeal (φ : R →ₐ[O] S) (A : CommAlgCat.{v} R) : Ideal A :=
  (RingHom.ker φ.toRingHom).map (algebraMap R A)

private def testReduction (φ : R →ₐ[O] S) (A : CommAlgCat.{v} R) :
    A →ₐ[R] (A ⧸ testIdeal φ A) :=
  Ideal.Quotient.mkₐ R (testIdeal φ A)

/-- Equality of pointed series over the smaller base implies equality when evaluated
and reduced modulo the extended coefficient kernel. -/
private theorem eval_eq_after_reduction (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    {κ : Type} {C D : CoordinateMap R κ τ}
    (he : C.map φ.toRingHom = D.map φ.toRingHom)
    (A : CommAlgCat.{v} R) (x : SeriesPoint A κ Empty) :
    (SeriesPoint.eval (C.map (algebraMap R A)) x).map (testReduction φ A).toRingHom =
      (SeriesPoint.eval (D.map (algebraMap R A)) x).map (testReduction φ A).toRingHom := by
  let q : R →+* (A ⧸ testIdeal φ A) :=
    (testReduction φ A).toRingHom.comp (algebraMap R A)
  have hq : RingHom.ker φ.toRingHom ≤ RingHom.ker q := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  let ψ := φ.toRingHom.liftOfSurjective hφ ⟨q, hq⟩
  have hψ : ψ.comp φ.toRingHom = q := φ.toRingHom.liftOfSurjective_comp hφ ⟨q, hq⟩
  rw [SeriesPoint.map_eval, SeriesPoint.map_eval,
    CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp]
  change SeriesPoint.eval (C.map q) _ = SeriesPoint.eval (D.map q) _
  rw [← hψ, ← CoordinateMap.map_ringHom_comp, ← CoordinateMap.map_ringHom_comp, he]

private def coordinateEval (N : ModuleLaw O R τ) {κ : Type} (C : CoordinateMap R κ τ)
    (A : CommAlgCat.{v} R) (x : SeriesPoint A κ Empty) : N.AlgebraPoint A :=
  SeriesPoint.eval (C.map (algebraMap R A)) x

/-- Scalar multiplication kills the differences of all pairs of evaluations
whose pointed coordinate maps agree after a nilpotent reduction. -/
private theorem exists_smul_eval_eq (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    (hI : IsNilpotent (RingHom.ker φ.toRingHom)) (hN : N.IsPiPowerTorsion π) :
    ∃ k : ℕ, ∀ {κ : Type} (C D : CoordinateMap R κ τ),
      C.map φ.toRingHom = D.map φ.toRingHom →
      ∀ (A : CommAlgCat.{v} R) (x : SeriesPoint A κ Empty),
        π ^ k • coordinateEval N C A x = π ^ k • coordinateEval N D A x := by
  obtain ⟨d, hd⟩ := hI
  obtain ⟨k, hk⟩ := exists_smul_eq_zero_of_bounded_coords hN d
  refine ⟨k, fun {κ} C D he A x => ?_⟩
  let y := coordinateEval N C A x
  let z := coordinateEval N D A x
  let q := testReduction φ A
  let B : CommAlgCat.{v} R := CommAlgCat.of R (A ⧸ testIdeal φ A)
  have hq : N.algebraMapPoints (B := B) q (y - z) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact eval_eq_after_reduction φ hφ he A x
  have hpow : (testIdeal φ A) ^ d = ⊥ := by
    rw [testIdeal, ← Ideal.map_pow, show RingHom.ker φ.toRingHom ^ d = ⊥ from hd,
      Ideal.map_bot]
  have hz : π ^ k • (y - z) = 0 := by
    apply hk
    intro i
    have hi := congrArg (fun w : N.AlgebraPoint B =>
      MvPowerSeries.constantCoeff (w.val i)) hq
    change MvPowerSeries.constantCoeff (MvPowerSeries.map q.toRingHom ((y - z).val i)) = 0 at hi
    rw [MvPowerSeries.constantCoeff_map] at hi
    have hm : MvPowerSeries.constantCoeff ((y - z).val i) ∈ testIdeal φ A :=
      Ideal.Quotient.eq_zero_iff_mem.mp hi
    have hp := Ideal.pow_mem_pow hm d
    rwa [hpow, Ideal.mem_bot] at hp
  rwa [smul_sub, sub_eq_zero] at hz

namespace Hom

/-- Integral formal homomorphisms out of a scalar-divisible law are rigid over
nilpotent thickenings when the target points are scalar-power torsion. -/
theorem map_injective_of_nilpotent (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiPowerTorsion π) :
    Function.Injective (mapLinear (M := M) (N := N) φ) := by
  obtain ⟨k, hk⟩ := exists_smul_eval_eq φ hφ hI hN
  intro f g he
  have hcomp : f.comp (M.scalarHom (π ^ k)) = g.comp (M.scalarHom (π ^ k)) := by
    rw [comp_scalarHom, comp_scalarHom]
    apply ext_onAlgebraPoints
    intro A x
    simp only [onAlgebraPoints_comp, scalarHom_onAlgebraPoints]
    exact hk _ _ (congrArg (fun h => h.toHom.toCoordinateMap) he) A x
  exact (hM.scalarPower_locallySurjective k).comp_right_cancel hcomp

omit [Finite σ] [Finite τ] in
private theorem exists_coordinateMap_lift (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    (D : CoordinateMap S σ τ) : ∃ C : CoordinateMap R σ τ, C.map φ.toRingHom = D := by
  classical
  let C : CoordinateMap R σ τ := {
    series := fun i μ =>
      if μ = 0 then 0 else (hφ (MvPowerSeries.coeff μ (D.series i))).choose
    constantCoeff_eq_zero := fun i => by
      change (if (0 : σ →₀ ℕ) = 0 then 0 else
        (hφ (MvPowerSeries.coeff 0 (D.series i))).choose) = 0
      simp }
  refine ⟨C, CoordinateMap.ext (funext fun i => ?_)⟩
  ext μ
  rw [CoordinateMap.map_series, MvPowerSeries.coeff_map]
  change φ (if μ = 0 then 0 else (hφ (MvPowerSeries.coeff μ (D.series i))).choose) = _
  by_cases hμ : μ = 0
  · subst μ
    simp only [eq_self, ite_true, map_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      D.constantCoeff_eq_zero]
  · rw [ite_eq_right hμ]
    exact (hφ _).choose_spec

set_option backward.isDefEq.respectTransparency false in
/-- Any homomorphism over a nilpotent quotient lifts after multiplication by
a power of the distinguished scalar. -/
theorem exists_lift_smul_of_nilpotent (φ : R →ₐ[O] S) (hφ : Function.Surjective φ)
    (hI : IsNilpotent (RingHom.ker φ.toRingHom)) (hN : N.IsPiPowerTorsion π)
    (f₀ : Hom (M.map φ) (N.map φ)) :
    ∃ (k : ℕ) (f : Hom M N), f.map φ = π ^ k • f₀ := by
  obtain ⟨k, hk⟩ := exists_smul_eval_eq φ hφ hI hN
  obtain ⟨C, hC⟩ := exists_coordinateMap_lift φ hφ f₀.toHom.toCoordinateMap
  let Φ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A) : N.AlgebraPoint A :=
    π ^ k • coordinateEval N C A x
  have hnat : IsNaturalOnPoints Φ := by
    intro A B ψ x
    dsimp only [Φ]
    rw [map_smul]
    congr 1
    exact CoordinateMap.isNaturalPointMap_eval C ψ x
  have hadd (A : CommAlgCat.{v} R) (x y : M.AlgebraPoint A) :
      Φ A (x + y) = Φ A x + Φ A y := by
    let L := C.comp M.groupLaw.addition
    let D := N.groupLaw.addition.comp
      ((C.comp CoordinateMap.fst).pair (C.comp CoordinateMap.snd))
    have he : L.map φ.toRingHom = D.map φ.toRingHom := by
      dsimp only [L, D]
      simp only [CoordinateMap.map_comp, CoordinateMap.map_pair,
        CoordinateMap.map_fst, CoordinateMap.map_snd, hC]
      exact f₀.toHom.map_add
    have hh := hk L D he A (SeriesPoint.pair x y)
    dsimp only [Φ]
    rw [← smul_add]
    simp only [L, D, coordinateEval, CoordinateMap.map_comp, CoordinateMap.map_pair,
      CoordinateMap.map_fst, CoordinateMap.map_snd, SeriesPoint.eval_comp,
      SeriesPoint.eval_pair, SeriesPoint.eval_fst, SeriesPoint.eval_snd] at hh
    exact hh
  have hsmul (A : CommAlgCat.{v} R) (a : O) (x : M.AlgebraPoint A) :
      Φ A (a • x) = a • Φ A x := by
    let L := C.comp (M.action a).toCoordinateMap
    let D := (N.action a).toCoordinateMap.comp C
    have he : L.map φ.toRingHom = D.map φ.toRingHom := by
      dsimp only [L, D]
      rw [CoordinateMap.map_comp, CoordinateMap.map_comp, hC]
      exact congrArg CommLaw.Hom.toCoordinateMap (f₀.commutes a)
    have hh := hk L D he A x
    simp only [L, D, coordinateEval, CoordinateMap.map_comp, SeriesPoint.eval_comp] at hh
    dsimp only [Φ]
    rw [smul_comm a (π ^ k)]
    exact hh
  let f : Hom M N := ofNatural Φ hnat hadd hsmul
  have hf : f.toHom.toCoordinateMap = ((N.action (π ^ k)).toCoordinateMap.comp C) := by
    apply CoordinateMap.ext_of_eval
    intro A x
    let x' : M.AlgebraPoint A := x
    calc
      f.onAlgebraPoints x' = Φ A x' := onAlgebraPoints_ofNatural hnat hadd hsmul A x'
      _ = _ := by
        rw [CoordinateMap.map_comp, SeriesPoint.eval_comp]
        rfl
  refine ⟨k, f, Hom.ext (CommLaw.Hom.ext ?_)⟩
  change f.toHom.toCoordinateMap.map φ.toRingHom =
    ((N.map φ).action (π ^ k)).toCoordinateMap.comp f₀.toHom.toCoordinateMap
  rw [hf, CoordinateMap.map_comp, hC]
  rfl

end Hom
end Langlands.FormalGroup.ModuleLaw
