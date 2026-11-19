import Langlands.Geometry.FormalGroup.DivisionOrderRationalTwist
import Mathlib.Algebra.Ring.Action.ConjAct

/-! # Composition of division-unit quasi-isogenies -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel ModuleLaw

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]

/-- The inverse-conjugation convention on the original division algebra. -/
def divisionConjugation (g : Dˣ) : D ≃ₐ[K] D where
  __ := MulSemiringAction.toRingEquiv (ConjAct Dˣ) D (ConjAct.toConjAct g⁻¹)
  commutes' k := by
    change ((g⁻¹ : Dˣ) : D) * algebraMap K D k * (((g⁻¹ : Dˣ)⁻¹ : Dˣ) : D) =
      algebraMap K D k
    rw [inv_inv, ← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]

@[simp]
theorem divisionConjugation_apply (g : Dˣ) (d : D) :
    divisionConjugation K D g d = ((g⁻¹ : Dˣ) : D) * d * (g : D) := by
  change ((g⁻¹ : Dˣ) : D) * d * (((g⁻¹ : Dˣ)⁻¹ : Dˣ) : D) = _
  rw [inv_inv]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

theorem divisionConjugation_coe (g : Dˣ) (a : IntegerRing K D) :
    divisionConjugation K D g (a : D) = (conjugation K D g a : D) := by
  rw [divisionConjugation_apply, conjugation_coe]

variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] R σ}

/-- Twisting the integer order conjugates the extended action on every element of the division algebra. -/
theorem rationalAction_twist (E : OrderAction (IntegerRing K D) M) (g : Dˣ) :
    rationalAction K D (twist K D E g) =
      (rationalAction K D E).comp (divisionConjugation K D g).toAlgHom := by
  apply algHom_ext_onIntegers K D
  intro a
  change rationalAction K D (twist K D E g) (a : D) =
    rationalAction K D E (divisionConjugation K D g (a : D))
  rw [rationalAction_coe, twist_action, divisionConjugation_coe, rationalAction_coe]

theorem rationalAction_twist_apply (E : OrderAction (IntegerRing K D) M) (g : Dˣ) (d : D) :
    rationalAction K D (twist K D E g) d =
      rationalAction K D E (((g⁻¹ : Dˣ) : D) * d * (g : D)) := by
  rw [rationalAction_twist, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, divisionConjugation_apply]

private theorem orderAction_eq {E E' : OrderAction (IntegerRing K D) M}
    (h : E.action = E'.action) : E = E' := by
  cases E
  cases E'
  cases h
  rfl

@[simp]
theorem twist_one (E : OrderAction (IntegerRing K D) M) : twist K D E 1 = E := by
  apply orderAction_eq K D
  apply RingHom.ext
  intro a
  rw [twist_action, conjugation_one]
  rfl

/-- Twisting by `g` and then by `h` conjugates by their product `h * g`. -/
theorem twist_twist (E : OrderAction (IntegerRing K D) M) (g h : Dˣ) :
    twist K D (twist K D E g) h = twist K D E (h * g) := by
  apply orderAction_eq K D
  apply RingHom.ext
  intro a
  rw [twist_action, twist_action, twist_action, conjugation_mul, AlgEquiv.trans_apply]

private theorem cast_quasiIsogeny_eq {E E' E'' : OrderAction (IntegerRing K D) M}
    (h : E' = E'') {f : OrderAction.QuasiIsogeny K E E'} {f' : OrderAction.QuasiIsogeny K E E''}
    (hf : f.hom.val = f'.hom.val) :
    cast (congrArg (fun X => OrderAction.QuasiIsogeny K E X) h) f = f' := by
  subst E''
  exact OrderAction.QuasiIsogeny.ext (OrderAction.RationalHom.ext hf)

/-- The identity unit gives the actual identity quasi-isogeny under the target identification. -/
theorem twistQuasiIsogeny_one (E : OrderAction (IntegerRing K D) M) :
    cast (congrArg (fun X => OrderAction.QuasiIsogeny K E X) (twist_one K D E))
      (twistQuasiIsogeny K D E 1) = OrderAction.QuasiIsogeny.refl (F := K) E := by
  apply cast_quasiIsogeny_eq K D (twist_one K D E)
  change rationalAction K D E (((1 : Dˣ)⁻¹ : Dˣ) : D) = 1
  simp

/-- The whole forward tensor of the composite is the inverse action of the product. -/
theorem twistQuasiIsogeny_mul_hom_val (E : OrderAction (IntegerRing K D) M) (g h : Dˣ) :
    ((twistQuasiIsogeny K D E g).trans (twistQuasiIsogeny K D (twist K D E g) h)).hom.val =
      (twistQuasiIsogeny K D E (h * g)).hom.val := by
  change rationalAction K D (twist K D E g) ((h⁻¹ : Dˣ) : D) *
    rationalAction K D E ((g⁻¹ : Dˣ) : D) = rationalAction K D E (((h * g)⁻¹ : Dˣ) : D)
  rw [rationalAction_twist_apply, ← map_mul]
  simp [mul_assoc]

/-- Composition agrees as a full-order quasi-isogeny after identifying the two target actions. -/
theorem twistQuasiIsogeny_mul (E : OrderAction (IntegerRing K D) M) (g h : Dˣ) :
    cast (congrArg (fun X => OrderAction.QuasiIsogeny K E X) (twist_twist K D E g h))
      ((twistQuasiIsogeny K D E g).trans (twistQuasiIsogeny K D (twist K D E g) h)) =
      twistQuasiIsogeny K D E (h * g) :=
  cast_quasiIsogeny_eq K D (twist_twist K D E g h) (twistQuasiIsogeny_mul_hom_val K D E g h)

/-- A central field unit gives the inverse scalar in the whole rational endomorphism algebra. -/
theorem twistQuasiIsogeny_scalar_hom_val (E : OrderAction (IntegerRing K D) M) (a : Kˣ) :
    (twistQuasiIsogeny K D E (Units.map (algebraMap K D).toMonoidHom a)).hom.val =
      ((a⁻¹ : Kˣ) : K) • RationalHom.id M :=
  (rationalAction K D E).commutes ((a⁻¹ : Kˣ) : K)

end Langlands.FormalGroup.LocalDivision
