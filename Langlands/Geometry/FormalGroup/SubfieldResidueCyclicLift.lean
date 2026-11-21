import Langlands.Geometry.FormalGroup.DrinfeldSubfieldCharacters
import Langlands.Algebra.LocalDivisionSubfieldHensel

/-! # Finite-order lifts of the embedded unramified residue units -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

/-- An integral root of unity whose actual residue generates the residue units. -/
structure ResidueCyclicLift (C : Type s) [CommRing C] [IsLocalRing C] where
  value : C
  residueOrder : orderOf (IsLocalRing.residue C value) = Nat.card (IsLocalRing.ResidueField C) - 1
  pow_eq_one : value ^ (Nat.card (IsLocalRing.ResidueField C) - 1) = 1

namespace ResidueCyclicLift

variable (C : Type s) [CommRing C] [HenselianLocalRing C]
variable [Finite (IsLocalRing.ResidueField C)]

/-- Lift a generator through the simple roots of the corresponding roots-of-unity polynomial. -/
theorem exists_lift : Nonempty (ResidueCyclicLift C) := by
  let κ := IsLocalRing.ResidueField C
  let : Fintype κ := Fintype.ofFinite κ
  let q := Nat.card κ
  let m := q - 1
  have hq : 1 < q := Finite.one_lt_card
  have hm : m ≠ 0 := Nat.sub_ne_zero_of_lt hq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κˣ)
  have hgorder : orderOf (g : κ) = m := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hgm : (g : κ) ^ m = 1 := by rw [← hgorder, pow_orderOf_eq_one]
  have hq₀ : (q : κ) = 0 := by
    simpa only [q, Nat.card_eq_fintype_card] using FiniteField.cast_card_eq_zero κ
  have hm₀ : (m : κ) ≠ 0 := by
    change ((q - 1 : ℕ) : κ) ≠ 0
    rw [Nat.cast_sub hq.le, hq₀, Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  let f : Polynomial C := Polynomial.X ^ m - Polynomial.C 1
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C 1 hm
  let r := IsLocalRing.residue C
  have hroot : f.eval₂ r (g : κ) = 0 := by simp [f, hgm]
  have hder : f.derivative.eval₂ r (g : κ) ≠ 0 := by
    simpa [f, Polynomial.derivative_X_pow] using mul_ne_zero hm₀ (pow_ne_zero (m - 1) g.ne_zero)
  have hh : HenselianLocalRing C := inferInstance
  have hiff := (HenselianLocalRing.TFAE C).out 1 3
  obtain ⟨a, ha, hred⟩ := hiff.mp hh
    r IsLocalRing.residue_surjective f hf (g : κ) hroot hder
  refine ⟨⟨a, ?_, ?_⟩⟩
  · exact (congrArg orderOf hred).trans hgorder
  · change Polynomial.eval a (Polynomial.X ^ m - Polynomial.C 1 : Polynomial C) = 0 at ha
    simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] using ha

/-- The integral generator chosen by the Henselian residue lift. -/
def chooseLift : ResidueCyclicLift C := Classical.choice (exists_lift C)

end ResidueCyclicLift

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

/-- The actual residue of the unramified integer subfield has cardinality `q^d`. -/
theorem subfieldResidue_card (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    Nat.card (IsLocalRing.ResidueField (SubfieldIntegerRing K D ι)) =
      (Nat.card 𝓀[K]) ^ CentralSimple.reducedDegree K D := by
  let C := SubfieldIntegerRing K D ι
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Finite (IsLocalRing.ResidueField C) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪[K]) (S := C) inferInstance
  let : Fintype (IsLocalRing.ResidueField C) := Fintype.ofFinite _
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  calc
    Nat.card (IsLocalRing.ResidueField C) = Fintype.card (IsLocalRing.ResidueField C) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card 𝓀[K] ^ Module.finrank 𝓀[K] (IsLocalRing.ResidueField C) :=
      Module.card_eq_pow_finrank
    _ = (Nat.card 𝓀[K]) ^ CentralSimple.reducedDegree K D := by
      rw [subfieldResidue_finrank ι hL, Fintype.card_eq_nat_card]

/-- Choose the actual integral generator with order the full residue-unit order. -/
def subfieldResidueCyclicLift (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    ResidueCyclicLift (SubfieldIntegerRing K D ι) := by
  let C := SubfieldIntegerRing K D ι
  let : FiniteDimensional K L := hL.1
  let : HenselianLocalRing C := localDivisionSubfield_henselian K D ι
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Finite (IsLocalRing.ResidueField C) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪[K]) (S := C) inferInstance
  exact ResidueCyclicLift.chooseLift C

end Langlands.FormalGroup.LocalDivision
