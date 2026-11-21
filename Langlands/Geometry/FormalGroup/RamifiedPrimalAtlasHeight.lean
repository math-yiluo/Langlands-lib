import Langlands.Geometry.FormalGroup.PrimalAtlasUniformizerHeight
import Langlands.Geometry.FormalGroup.ScalarCompositesIsogeny

/-! # Actual height of the split primal atlas for arbitrary positive ramification -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable {a π : O} {b : Oˣ} {e : ℕ}

/-- If a divisible scalar is an integral unit times a positive uniformizer power,
all uniformizer powers act by actual isogenies. -/
theorem IsPiDivisible.uniformizerPower_isIsogeny (hA : M.IsPiDivisible a)
    (ha : a = (b : O) * π ^ e) (he : 0 < e) (n : ℕ) : (M.scalarHom (π ^ n)).IsIsogeny := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  let c := (b : O) ^ n * π ^ (k * n)
  have hsplit : c * π ^ n = a ^ n := by
    rw [ha, mul_pow, ← pow_mul, Nat.succ_mul, pow_add]
    exact mul_assoc _ _ _
  have hg : (M.scalarHom c).comp (M.scalarHom (π ^ n)) = M.scalarHom (a ^ n) := by
    rw [← scalarHom_mul, hsplit]
  have hf : (M.scalarHom (π ^ n)).comp (M.scalarHom c) = M.scalarHom (a ^ n) := by
    rw [← scalarHom_mul, mul_comm (π ^ n), hsplit]
  exact Hom.isIsogeny_of_scalarComposites_overRing hA hA hg hf

/-- Divisibility by the ramified scalar gives actual uniformizer divisibility. -/
theorem IsPiDivisible.of_ramifiedScalar (hA : M.IsPiDivisible a)
    (ha : a = (b : O) * π ^ e) (he : 0 < e) : M.IsPiDivisible π :=
  hA.of_unit_mul_pow ha he (fun n => (hA.uniformizerPower_isIsogeny ha he n).2)

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

/-- The special primal atlas of a split target has square height for every positive
ramification exponent, using the supplied actual square-height frame. -/
def HasSplitSpecialTangent.primalHeightSquaredAtlas (h : HasSplitSpecialTangent ι X)
    (A : frame.order.DivisionImage M)
    (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] kW))
    (hFrame : (A.centralModule hs).HasPiHeight ϖ (Nat.card 𝓀[K]) (d ^ 2))
    (hϖ : Irreducible ϖ) {e f : ℕ} (he : 0 < e) {a : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (a : 𝒪[K]) * ϖ ^ e) (hq : Nat.card 𝓀[K] = prime ^ f) :
    SpecialAtlas.HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := T.obj) ϖ := by
  have hM := A.isPiDivisible frame.divisible
  let hs' := A.structuralCentralTangent hs
  have hC := A.order.centralModule_isPiDivisible_natCast hs' prime hM
  have hFrame' : (A.centralModule hs).HasPiHeight ϖ (prime ^ f) (d ^ 2) := hq ▸ hFrame
  have hPadic := A.order.hasPiHeight_natCast_of_centralModule hs' hM (hFrame'.unit_mul_pow hC hp)
  exact h.primalFiniteHeightAtlas A hs hFrame hϖ he hp hq (fun b n =>
    ((h.primalSpecialAtlas_hasPiHeight_p A hPadic b).piDivisible.uniformizerPower_isIsogeny hp he n).2)

end Langlands.FormalGroup.Harris
