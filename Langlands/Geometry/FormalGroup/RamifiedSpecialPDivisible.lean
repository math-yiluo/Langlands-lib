import Langlands.Geometry.FormalGroup.SpecialModule
import Langlands.Geometry.FormalGroup.ScalarRamificationHeight
import Langlands.Geometry.FormalGroup.FormalModulePDivisibleMorphism
import Langlands.Geometry.FormalGroup.PDivisibleSplitOrderAction

/-! # The actual p-divisible tower of a special formal division module -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u v s

open CategoryTheory AlgebraicGeometry ValuativeRel

namespace Langlands.FormalGroup.ModuleLaw.IsPiDivisible

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable {π a : O} {b : Oˣ} {e : ℕ}

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

/-- Divisibility by a scalar persists under passage to a positive power times a unit,
with actual represented kernels at every new exponent. -/
theorem unit_mul_pow (hπ : M.IsPiDivisible π) (ha : a = (b : O) * π ^ e) (he : 0 < e) :
    M.IsPiDivisible a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hπ.base_nilpotent
    refine ⟨n, ?_⟩
    rw [ha, map_mul, map_pow, mul_pow, ← pow_mul, Nat.mul_comm e n, pow_mul, hn, zero_pow he.ne', mul_zero]
  · intro A x
    obtain ⟨n, hn⟩ := hπ.torsion A x
    have hle : n ≤ e * n := Nat.le_mul_of_pos_left n he
    have hkill : (π ^ (e * n)) • x = 0 := by
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hn, smul_zero]
    refine ⟨n, ?_⟩
    rw [ha, mul_pow, ← pow_mul, mul_smul, hkill, smul_zero]
  · rw [ha, scalarHom_mul]
    exact (M.scalarUnitIso b).isFppfLocallySurjective.comp (hπ.scalarPower_locallySurjective e)
  · intro n
    obtain ⟨P⟩ := hπ.scalarPower_finiteKernel (e * n)
    rw [ha, mul_pow, ← pow_mul]
    exact ⟨P.transport (M.scalarKernelIso_unit_mul (b ^ n) (π ^ (e * n)))⟩

end Langlands.FormalGroup.ModuleLaw.IsPiDivisible

namespace Langlands.FormalGroup.LocalDivision.SpecialModule.HeightSquaredModule

open CentralDivision CentralSimple ModuleLaw GroupScheme.Cartier

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R] {π : 𝒪[K]}
variable (X : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := R) π)
variable {p e f : ℕ} {b : 𝒪[K]ˣ}
variable (hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e) (he : 0 < e)

include hp he in
/-- The prime-height certificate comes from the actual central scalar kernels. -/
theorem hasPrimeHeight (hq : Nat.card 𝓀[K] = p ^ f) :
    X.val.formalModule.HasPiHeight (p : 𝒪[K]) p (e * f * (reducedDegree K D) ^ 2) := by
  have h := X.property.2
  rw [hq] at h
  exact h.unit_mul_pow (h.piDivisible.unit_mul_pow hp he) hp

variable [Fact p.Prime]

/-- The actual p-divisible group of the special formal division module. -/
def pDivisibleGroup : PDivisibleGroup (CommRingCat.of R) p :=
  (X.property.2.piDivisible.unit_mul_pow hp he).pDivisibleGroup

/-- Its height on the actual finite group schemes is the central height times
ramification index and residue degree. -/
theorem pDivisibleGroup_hasHeight (hq : Nat.card 𝓀[K] = p ^ f) :
    (X.pDivisibleGroup hp he).HasHeight (e * f * (reducedDegree K D) ^ 2) :=
  IsPiDivisible.pDivisibleGroup_hasHeight (X.hasPrimeHeight hp he hq)

/-- The actual division order acts on these finite group schemes. -/
def pDivisibleAction : IntegerRing K D →+* End (X.pDivisibleGroup hp he) :=
  X.val.order.pDivisibleAction (X.property.2.piDivisible.unit_mul_pow hp he)

/-- The split tower uses the actual p-power kernels and the full Cartier dual tower. -/
def splitPDivisibleGroup (hExact : FiniteCartierDualExactnessStatement.{v}) :
    PDivisibleGroup (CommRingCat.of R) p :=
  (X.pDivisibleGroup hp he).splitWithDual hExact

/-- The tautological polarization on the actual split tower. -/
def splitPDivisiblePolarization (hExact : FiniteCartierDualExactnessStatement.{v}) :
    (X.splitPDivisibleGroup hp he hExact).PrincipalPolarization :=
  (X.pDivisibleGroup hp he).splitPrincipalPolarization hExact

/-- The split division order acts on the actual polarized product with the exchange adjoint. -/
def splitPDivisibleAction (hExact : FiniteCartierDualExactnessStatement.{v}) :
    (IntegerRing K D)ᵐᵒᵖ × IntegerRing K D →+* End (X.splitPDivisibleGroup hp he hExact) :=
  PDivisibleGroup.splitOrderAction (X.pDivisibleAction hp he) hExact

end Langlands.FormalGroup.LocalDivision.SpecialModule.HeightSquaredModule
