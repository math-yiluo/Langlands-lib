import Langlands.Geometry.FormalGroup.PrimalAtlasUniformizerHeight

/-! # Square height of the split primal atlas at ramification index one -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable {a π : O} {b : Oˣ}

/-- A unit times a scalar has the same finite locally free power kernels as the scalar. -/
theorem IsPiDivisible.scalarPower_finiteKernel_of_unit_mul (hA : M.IsPiDivisible a)
    (ha : a = (b : O) * π) (n : ℕ) : (M.scalarHom (π ^ n)).HasFiniteLocallyFreeKernel := by
  have hk := hA.scalarPower_finiteKernel n
  rw [ha, mul_pow] at hk
  obtain ⟨K⟩ := hk
  exact ⟨K.transport (M.scalarKernelIso_unit_mul (b ^ n) (π ^ n)).symm⟩

/-- Divisibility is invariant under changing a scalar by a unit. -/
theorem IsPiDivisible.of_unit_mul (hA : M.IsPiDivisible a) (ha : a = (b : O) * π) :
    M.IsPiDivisible π :=
  hA.of_unit_mul_pow (e := 1) (by simpa only [pow_one] using ha) Nat.one_pos
    (hA.scalarPower_finiteKernel_of_unit_mul ha)

end Langlands.FormalGroup.ModuleLaw

namespace Langlands.FormalGroup.Harris

open ValuativeRel ModuleLaw LocalDivision

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
attribute [local instance] primalDivisionPadicAlgebra

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Algebra ℤ_[prime] 𝒪[K]]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable {ϖ : 𝒪[K]} {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw ℤ_[prime] (ResidueRing W (algebraMap 𝒪[K] W ϖ)) σ}

local notation "kW" => ResidueRing W (algebraMap 𝒪[K] W ϖ)
local notation "d" => CentralSimple.reducedDegree K D

/-- When p is a unit times the central uniformizer, the actual primal frame of square
height gives square height on the actual special atlas of the split target. -/
def HasSplitSpecialTangent.primalUnramifiedHeightAtlas (h : HasSplitSpecialTangent ι X)
    (A : frame.order.DivisionImage M)
    (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] kW))
    (hFrame : (A.centralModule hs).HasPiHeight ϖ (Nat.card 𝓀[K]) (d ^ 2))
    (hϖ : Irreducible ϖ) {f : ℕ} {a : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (a : 𝒪[K]) * ϖ) (hq : Nat.card 𝓀[K] = prime ^ f) :
    SpecialAtlas.HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := T.obj) ϖ := by
  have hM := A.isPiDivisible frame.divisible
  let hs' := A.structuralCentralTangent hs
  have hC := A.order.centralModule_isPiDivisible_natCast hs' prime hM
  have hFrame' : (A.centralModule hs).HasPiHeight ϖ (prime ^ f) (d ^ 2) := hq ▸ hFrame
  have hp' : (prime : 𝒪[K]) = (a : 𝒪[K]) * ϖ ^ 1 := by simpa only [pow_one] using hp
  have hPadic := A.order.hasPiHeight_natCast_of_centralModule hs' hM (hFrame'.unit_mul_pow hC hp')
  exact h.primalFiniteHeightAtlas A hs hFrame hϖ Nat.one_pos hp' hq (fun b n =>
    (h.primalSpecialAtlas_hasPiHeight_p A hPadic b).piDivisible.scalarPower_finiteKernel_of_unit_mul hp n)

end Langlands.FormalGroup.Harris
