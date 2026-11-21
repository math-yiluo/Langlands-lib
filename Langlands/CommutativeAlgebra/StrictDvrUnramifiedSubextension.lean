import Langlands.CommutativeAlgebra.StrictHenselianDvrUniformizer
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # Finite Galois subextensions of a uniformizer-preserving trait -/

noncomputable section

open IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.CommutativeAlgebra.StrictHenselianDvrAt

variable {R K L : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] {π : R}

/-- The finite field embedding takes the original integral closure into the
selected strictly Henselian DVR. -/
def integralClosureMap (T : StrictHenselianDvrAt R K π) :
    letI := T.fractionMap.toRingHom.toAlgebra
    (L →ₐ[K] FractionRing T.ring) → (integralClosure R L →ₐ[R] T.ring) := by
  letI := T.fractionMap.toRingHom.toAlgebra
  let : IsScalarTower R K (FractionRing T.ring) := IsScalarTower.of_algHom T.fractionMap
  intro e
  let h (a : integralClosure R L) :
      IsIntegral T.ring (e (a : L)) := (a.property.map (e.restrictScalars R)).tower_top
  let f (a : integralClosure R L) :=
    IsIntegralClosure.mk' T.ring (e (a : L)) (h a)
  have hf (a : integralClosure R L) : algebraMap T.ring (FractionRing T.ring) (f a) = e (a : L) :=
    IsIntegralClosure.algebraMap_mk' _ _ _
  refine
    { toFun := f
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ } <;>
    intros <;> apply IsFractionRing.injective T.ring (FractionRing T.ring)
  · simp only [hf, map_one, OneMemClass.coe_one]
  · simp only [hf, map_mul, MulMemClass.coe_mul]
  · simp only [hf, map_zero, ZeroMemClass.coe_zero]
  · simp only [hf, map_add, AddMemClass.coe_add]
  · rw [hf, ← IsScalarTower.algebraMap_apply R T.ring (FractionRing T.ring)]
    exact (e.restrictScalars R).commutes _

/-- The integral closure of a residue-characteristic-zero DVR in a finite
Galois extension embedding into the fraction field of the uniformizer-preserving
strict trait is finite étale over the original DVR. -/
theorem etale_integralClosure (T : StrictHenselianDvrAt R K π) (hπ : Irreducible π)
    [CharZero (ResidueField R)] [FiniteDimensional K L] [IsGalois K L]
    (e : letI := T.fractionMap.toRingHom.toAlgebra; L →ₐ[K] FractionRing T.ring) :
    Algebra.Etale R (integralClosure R L) := by
  let S := integralClosure R L
  let f : S →ₐ[R] T.ring := T.integralClosureMap e
  have hcomp : f.toRingHom.comp (algebraMap R S) = algebraMap R T.ring := f.comp_algebraMap
  let p := maximalIdeal R
  let P : Ideal S := Ideal.comap f.toRingHom (maximalIdeal T.ring)
  let : IsLocalHom (algebraMap R T.ring) := T.localHom
  let : P.IsPrime := Ideal.IsPrime.comap _
  let : P.LiesOver p := (Ideal.liesOver_iff _ _).mpr (by
    change p = Ideal.comap (algebraMap R S) (Ideal.comap f.toRingHom (maximalIdeal T.ring))
    rw [Ideal.comap_comap, hcomp]
    exact (Ideal.liesOver_iff _ _).mp
      (inferInstance : (maximalIdeal T.ring).LiesOver p))
  have hP : p.map (algebraMap R S) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (Ideal.LiesOver.over (p := p) (P := P)).le
  have hram : Ideal.ramificationIdx' p P = 1 := by
    by_contra h
    have h₂ := (Ideal.ramificationIdx'_ne_one_iff hP).mp h
    have hmap := Ideal.map_mono (f := f.toRingHom) h₂
    rw [Ideal.map_map, hcomp, show p = Ideal.span {π} from hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, ← T.uniformizer.maximalIdeal_eq, Ideal.map_pow] at hmap
    have hle : P.map f.toRingHom ≤ maximalIdeal T.ring := Ideal.map_comap_le
    have hpow : (P.map f.toRingHom) ^ 2 ≤ (maximalIdeal T.ring) ^ 2 := by
      simpa only [pow_two] using Ideal.mul_mono hle hle
    have hn := (maximalIdeal T.ring).pow_right_strictAnti
      (IsDiscreteValuationRing.maximalIdeal T.ring).ne_bot
      (maximalIdeal.isMaximal T.ring).ne_top (show 1 < 2 by decide)
    exact hn.not_ge (by simpa only [pow_one] using hmap.trans hpow)
  let : CharZero R := ⟨fun a b h =>
    Nat.cast_injective (R := ResidueField R)
      (by simpa only [map_natCast] using congrArg (residue R) h)⟩
  let : Module.Finite R S := IsIntegralClosure.finite R K L S
  let : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R K L S
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    fun _ _ h => hRL (congrArg (fun a : S => (a : L)) h)
  let : Module.Flat R S := inferInstance
  let : Algebra.FormallyUnramified R S := Algebra.formallyUnramified_iff_forall.mpr (by
    intro q
    let Q := q.asIdeal
    have hQprime : Q.IsPrime := q.isPrime
    by_cases hQ : Q = ⊥
    · obtain rfl : q = (⊥ : PrimeSpectrum S) := PrimeSpectrum.ext hQ
      exact Algebra.isUnramifiedAt_bot
    have hQover : Q.under R = p := by
      have hne : Q.under R ≠ ⊥ := by
        intro hbot
        have : Q.LiesOver (⊥ : Ideal R) := (Ideal.liesOver_iff _ _).mpr hbot.symm
        exact hQ (Ideal.eq_bot_of_liesOver_bot R Q)
      exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hne)
    let : Q.LiesOver p := (Ideal.liesOver_iff _ _).mpr hQover.symm
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq R K L S
      (p := p) (P₁ := P) (P₂ := Q) ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩
    have hQram : Ideal.ramificationIdx' p Q = 1 := by
      rw [← hσ, Ideal.ramificationIdx'_comap_eq]
      exact hram
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver p Q
    let : CharZero p.ResidueField := charZero_of_injective_algebraMap
      (algebraMap (ResidueField R) p.ResidueField).injective
    exact (Algebra.isUnramifiedAt_iff_map_eq R p Q).mpr
      ⟨inferInstance, (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hQ
        (Ideal.map_le_iff_le_comap.mpr hQover.symm.le)).mp hQram⟩)
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Langlands.CommutativeAlgebra.StrictHenselianDvrAt
