import Langlands.Geometry.FormalGroup.DivisionOrderRationalAction
import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # Quasi-isogenies for division-unit twists -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {S : Type w} [CommRing S] [Algebra 𝒪[K] S]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] R σ}

/-- A division unit acts by the inverse unit from the original order action to the conjugated one. -/
def twistQuasiIsogeny (E : OrderAction (IntegerRing K D) M) (g : Dˣ) :
    OrderAction.QuasiIsogeny K E (twist K D E g) :=
  OrderAction.QuasiIsogeny.ofModuleQuasiIsogeny
    { hom := rationalAction K D E ((g⁻¹ : Dˣ) : D)
      inv := rationalAction K D E (g : D)
      inv_hom := by
        change rationalAction K D E (g : D) * rationalAction K D E ((g⁻¹ : Dˣ) : D) = 1
        rw [← map_mul, Units.mul_inv, map_one]
      hom_inv := by
        change rationalAction K D E ((g⁻¹ : Dˣ) : D) * rationalAction K D E (g : D) = 1
        rw [← map_mul, Units.inv_mul, map_one] }
    (fun a => by
      change rationalAction K D E ((g⁻¹ : Dˣ) : D) * RationalHom.ofHom (E.action a) =
        RationalHom.ofHom (E.action (conjugation K D g a)) *
          rationalAction K D E ((g⁻¹ : Dˣ) : D)
      rw [← rationalAction_coe K D E a, ← rationalAction_coe K D E (conjugation K D g a),
        ← map_mul, ← map_mul, conjugation_coe]
      simp [mul_assoc])

@[simp]
theorem twistQuasiIsogeny_hom_val (E : OrderAction (IntegerRing K D) M) (g : Dˣ) :
    (twistQuasiIsogeny K D E g).hom.val = rationalAction K D E ((g⁻¹ : Dˣ) : D) := rfl

@[simp]
theorem twistQuasiIsogeny_inv_val (E : OrderAction (IntegerRing K D) M) (g : Dˣ) :
    (twistQuasiIsogeny K D E g).inv.val = rationalAction K D E (g : D) := rfl

/-- Extending the formal coefficients preserves the complete quasi-isogeny to the twist. -/
@[simp]
theorem twistQuasiIsogeny_map (E : OrderAction (IntegerRing K D) M) (g : Dˣ)
    (θ : R →ₐ[𝒪[K]] S) :
    (twistQuasiIsogeny K D E g).map θ = twistQuasiIsogeny K D (E.map θ) g := by
  apply OrderAction.QuasiIsogeny.ext
  apply OrderAction.RationalHom.ext
  exact rationalAction_map_apply K D E θ ((g⁻¹ : Dˣ) : D)

/-- An integral unit gives the rationalization of the existing integral twist isomorphism. -/
@[simp]
theorem twistQuasiIsogeny_integerUnit (E : OrderAction (IntegerRing K D) M)
    (a : (IntegerRing K D)ˣ) :
    twistQuasiIsogeny K D E (integerUnit K D a) =
      OrderAction.QuasiIsogeny.ofIso (twistUnitIso K D E a) := by
  apply OrderAction.QuasiIsogeny.ext
  apply OrderAction.RationalHom.ext
  exact rationalAction_coe K D E (a⁻¹ : (IntegerRing K D)ˣ)

end Langlands.FormalGroup.LocalDivision
