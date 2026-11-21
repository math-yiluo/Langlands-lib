import Langlands.Geometry.FormalGroup.PrimalAtlasPadicHeight
import Langlands.Geometry.FormalGroup.ScalarRamificationHeight

/-! # The central uniformizer height on the split primal special atlas -/

noncomputable section

universe u s

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

/-- A calibration of p and the residue cardinality carries the frame's square height to
all primal chart laws with finite locally free central uniformizer kernels. -/
theorem HasSplitSpecialTangent.primalSpecialAtlas_hasHeightSquared (h : HasSplitSpecialTangent ι X)
    (A : frame.order.DivisionImage M)
    (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] kW))
    (hFrame : (A.centralModule hs).HasPiHeight ϖ (Nat.card 𝓀[K]) (d ^ 2))
    (hϖ : Irreducible ϖ) {e f : ℕ} (he : 0 < e) {a : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (a : 𝒪[K]) * ϖ ^ e) (hq : Nat.card 𝓀[K] = prime ^ f)
    (hk : ∀ (b : h.primalSpecialAtlas.atlas.opens) (n : ℕ),
      ((h.primalSpecialAtlas.atlas.chart b).scalarHom (ϖ ^ n)).HasFiniteLocallyFreeKernel) :
    h.primalSpecialAtlas.HasHeightSquared ϖ := by
  have hM := A.isPiDivisible frame.divisible
  let hs' := A.structuralCentralTangent hs
  have hC := A.order.centralModule_isPiDivisible_natCast hs' prime hM
  have hFrame' : (A.centralModule hs).HasPiHeight ϖ (prime ^ f) (d ^ 2) := hq ▸ hFrame
  have hPadic := A.order.hasPiHeight_natCast_of_centralModule hs' hM (hFrame'.unit_mul_pow hC hp)
  refine ⟨hϖ, ?_, fun b => ?_⟩
  · rw [IsScalarTower.algebraMap_apply 𝒪[K] W T.obj]
    exact T.property
  · have hChart := h.primalSpecialAtlas_hasPiHeight_p A hPadic b
    have hπ := hChart.piDivisible.of_unit_mul_pow hp he (hk b)
    rw [hq]
    exact hChart.of_unit_mul_pow hπ hp he

/-- The finite-height primal atlas built from the actual split framed object. -/
def HasSplitSpecialTangent.primalFiniteHeightAtlas (h : HasSplitSpecialTangent ι X)
    (A : frame.order.DivisionImage M)
    (hs : frame.order.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] kW))
    (hFrame : (A.centralModule hs).HasPiHeight ϖ (Nat.card 𝓀[K]) (d ^ 2))
    (hϖ : Irreducible ϖ) {e f : ℕ} (he : 0 < e) {a : 𝒪[K]ˣ}
    (hp : (prime : 𝒪[K]) = (a : 𝒪[K]) * ϖ ^ e) (hq : Nat.card 𝓀[K] = prime ^ f)
    (hk : ∀ (b : h.primalSpecialAtlas.atlas.opens) (n : ℕ),
      ((h.primalSpecialAtlas.atlas.chart b).scalarHom (ϖ ^ n)).HasFiniteLocallyFreeKernel) :
    SpecialAtlas.HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := T.obj) ϖ :=
  ⟨h.primalSpecialAtlas, h.primalSpecialAtlas_hasHeightSquared A hs hFrame hϖ he hp hq hk⟩

end Langlands.FormalGroup.Harris
