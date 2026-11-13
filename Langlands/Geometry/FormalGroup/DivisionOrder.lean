import Langlands.Geometry.FormalGroup.OrderAction
import Langlands.Algebra.LocalDivisionResidueScalar
import Langlands.Shimura.Unitary.LocalDivisionLevels

/-! # Actual local division orders and conjugation of formal order actions -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The actual integer subring of the canonical reduced-norm valuation. -/
abbrev IntegerRing := (localReducedNormValuation K D).integer

/-- Central integral scalars act on the actual division order. -/
instance integerAlgebra : Algebra 𝒪[K] (IntegerRing K D) :=
  (localDivisionIntegerMap K D).toAlgebra' (by
    intro a x
    apply Subtype.ext
    exact Algebra.commutes (a : K) (x : D))

@[simp]
theorem coe_algebraMap (a : 𝒪[K]) :
    (algebraMap 𝒪[K] (IntegerRing K D) a : D) = algebraMap K D (a : K) := rfl

/-- Multiplicativity makes the canonical valuation invariant under inner conjugation. -/
theorem value_conjugate (g : Dˣ) (a : D) :
    localReducedNormValuation K D ((g⁻¹ : Dˣ) * a * (g : D)) =
      localReducedNormValuation K D a := by
  let v := localReducedNormValuation K D
  have hg : v ((g⁻¹ : Dˣ) : D) * v (g : D) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  change v (((g⁻¹ : Dˣ) : D) * a * (g : D)) = v a
  rw [map_mul, map_mul]
  calc
    v ((g⁻¹ : Dˣ) : D) * v a * v (g : D) =
        v a * (v ((g⁻¹ : Dˣ) : D) * v (g : D)) := by ac_rfl
    _ = v a := by rw [hg, mul_one]

/-- Drinfeld's conjugation `a ↦ g⁻¹ a g` is an actual automorphism of the integer order. -/
def conjugation (g : Dˣ) : IntegerRing K D ≃ₐ[𝒪[K]] IntegerRing K D where
  toFun a := ⟨((g⁻¹ : Dˣ) : D) * (a : D) * (g : D), by
    change localReducedNormValuation K D _ ≤ 1
    rw [value_conjugate]
    exact a.prop⟩
  invFun a := ⟨(g : D) * (a : D) * ((g⁻¹ : Dˣ) : D), by
    change localReducedNormValuation K D _ ≤ 1
    have h := value_conjugate K D g⁻¹ (a : D)
    simpa only [inv_inv] using h.le.trans a.prop⟩
  left_inv a := by
    apply Subtype.ext
    change (g : D) * (((g⁻¹ : Dˣ) : D) * (a : D) * (g : D)) *
      ((g⁻¹ : Dˣ) : D) = a
    simp [mul_assoc]
  right_inv a := by
    apply Subtype.ext
    change ((g⁻¹ : Dˣ) : D) * ((g : D) * (a : D) *
      ((g⁻¹ : Dˣ) : D)) * (g : D) = a
    simp [mul_assoc]
  map_add' a b := by
    apply Subtype.ext
    change ((g⁻¹ : Dˣ) : D) * ((a : D) + (b : D)) * (g : D) =
      ((g⁻¹ : Dˣ) : D) * (a : D) * (g : D) +
        ((g⁻¹ : Dˣ) : D) * (b : D) * (g : D)
    simp only [mul_add, add_mul]
  map_mul' a b := by
    apply Subtype.ext
    change ((g⁻¹ : Dˣ) : D) * ((a : D) * (b : D)) * (g : D) =
      (((g⁻¹ : Dˣ) : D) * (a : D) * (g : D)) *
        (((g⁻¹ : Dˣ) : D) * (b : D) * (g : D))
    simp [mul_assoc]
  commutes' a := by
    apply Subtype.ext
    change ((g⁻¹ : Dˣ) : D) * algebraMap K D (a : K) * (g : D) =
      algebraMap K D (a : K)
    rw [← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]

@[simp]
theorem conjugation_coe (g : Dˣ) (a : IntegerRing K D) :
    (conjugation K D g a : D) = ((g⁻¹ : Dˣ) : D) * (a : D) * (g : D) := rfl

@[simp]
theorem conjugation_one :
    conjugation K D 1 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro a
  apply Subtype.ext
  simp

/-- The inverse-conjugation convention reverses the composition of automorphisms. -/
theorem conjugation_mul (g h : Dˣ) :
    conjugation K D (g * h) = (conjugation K D g).trans (conjugation K D h) := by
  apply AlgEquiv.ext
  intro a
  apply Subtype.ext
  simp [mul_assoc]

/-- Central field units induce the identity conjugation on the actual order. -/
theorem conjugation_scalar (a : Kˣ) :
    conjugation K D (Units.map (algebraMap K D).toMonoidHom a) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change algebraMap K D ((a⁻¹ : Kˣ) : K) * (x : D) *
      algebraMap K D (a : K) = (x : D)
  rw [Algebra.commutes, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

/-- An actual integer-order unit is a unit of the ambient division algebra. -/
def integerUnit (a : (IntegerRing K D)ˣ) : Dˣ :=
  Units.map (localReducedNormValuation K D).integer.subtype.toMonoidHom a

@[simp]
theorem integerUnit_coe (a : (IntegerRing K D)ˣ) :
    (integerUnit K D a : D) = ((a : IntegerRing K D) : D) := rfl

@[simp]
theorem conjugation_integerUnit (u : (IntegerRing K D)ˣ) (a : IntegerRing K D) :
    conjugation K D (integerUnit K D u) a =
      (u⁻¹ : (IntegerRing K D)ˣ) * a * (u : IntegerRing K D) := by
  apply Subtype.ext
  rfl

section NormComparison

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K

/-- The valuation order is the integer ring used to define the published division levels. -/
theorem integerRing_eq_levelIntegerRing :
    (localReducedNormValuation K D).integer =
      Shimura.LocalDivision.integerRing K D := by
  ext x
  exact (localDivisionNorm_le_one_iff K D x).symm

end NormComparison

variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {S : Type w} [CommRing S] [Algebra 𝒪[K] S]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] R σ}

/-- The formal module in Drinfeld's twist has the same formal O-module and conjugated order action. -/
def twist (E : ModuleLaw.OrderAction (IntegerRing K D) M) (g : Dˣ) :
    ModuleLaw.OrderAction (IntegerRing K D) M :=
  E.twist (conjugation K D g)

@[simp]
theorem twist_action (E : ModuleLaw.OrderAction (IntegerRing K D) M) (g : Dˣ)
    (a : IntegerRing K D) :
    (twist K D E g).action a = E.action (conjugation K D g a) := rfl

/-- Coefficient extension commutes with the actual conjugation twist. -/
theorem twist_map (E : ModuleLaw.OrderAction (IntegerRing K D) M)
    (g : Dˣ) (θ : R →ₐ[𝒪[K]] S) :
    (twist K D E g).map θ = twist K D (E.map θ) g := rfl

/-- An integer-order unit identifies a module with its conjugation twist. -/
def twistUnitIso (E : ModuleLaw.OrderAction (IntegerRing K D) M)
    (u : (IntegerRing K D)ˣ) :
    ModuleLaw.OrderAction.Iso E (twist K D E (integerUnit K D u)) where
  hom := ⟨E.action (u⁻¹ : (IntegerRing K D)ˣ), by
    intro a
    change E.action (u⁻¹ : (IntegerRing K D)ˣ) * E.action a =
      E.action (conjugation K D (integerUnit K D u) a) *
        E.action (u⁻¹ : (IntegerRing K D)ˣ)
    rw [conjugation_integerUnit, ← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]⟩
  inv := ⟨E.action (u : IntegerRing K D), by
    intro a
    change E.action (u : IntegerRing K D) *
        E.action (conjugation K D (integerUnit K D u) a) =
      E.action a * E.action (u : IntegerRing K D)
    rw [conjugation_integerUnit, ← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]⟩
  inv_hom := by
    apply Subtype.ext
    change E.action (u : IntegerRing K D) *
      E.action (u⁻¹ : (IntegerRing K D)ˣ) = 1
    rw [← map_mul, Units.mul_inv, map_one]
  hom_inv := by
    apply Subtype.ext
    change E.action (u⁻¹ : (IntegerRing K D)ˣ) *
      E.action (u : IntegerRing K D) = 1
    rw [← map_mul, Units.inv_mul, map_one]

@[simp]
theorem twistUnitIso_hom (E : ModuleLaw.OrderAction (IntegerRing K D) M)
    (u : (IntegerRing K D)ˣ) :
    (twistUnitIso K D E u).hom.val = E.action (u⁻¹ : (IntegerRing K D)ˣ) := rfl

@[simp]
theorem twistUnitIso_inv (E : ModuleLaw.OrderAction (IntegerRing K D) M)
    (u : (IntegerRing K D)ˣ) :
    (twistUnitIso K D E u).inv.val = E.action (u : IntegerRing K D) := rfl

end Langlands.FormalGroup.LocalDivision
