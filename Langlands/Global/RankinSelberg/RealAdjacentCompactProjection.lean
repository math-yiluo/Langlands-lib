import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection
import Langlands.Global.RankinSelberg.RealPrincipalSeriesEvaluationReduction
import Langlands.Global.RankinSelberg.RealTriangularInversion
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-! # Finite compact projections of real Whittaker coefficients

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexJacquet (exists_compactPairing_expansion hasFiniteCompactConvolutionKernel_of_finite_translates)

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "ι" => GeneralLinear.inverseTranspose (r + 1) ℝ
local notation "wd" => ArchimedeanLocal.dualFunction (r + 1)

/-- The inverse transpose of an orthogonal matrix is the matrix itself. -/
theorem inverseTranspose_orthogonal {g : G} (hg : g ∈ unitaryCompact ℝ (r + 1)) : ι g = g :=
  GodementJacquet.realInverseTranspose_unitary_eq (r + 1) ⟨g, hg⟩

section Compact

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

variable (r) in
/-- A compact convolution formula on compact-finite standard vectors, compatible with a
Whittaker intertwiner, gives paired finite Whittaker and compact-pairing expansions. The
compact group `K` maps onto the orthogonal group. -/
def RealLocalCompactProjectionReductionStatement : Prop :=
  ∀ (iK : K →* G), Continuous iK → (∀ k, iK k ∈ unitaryCompact ℝ (r + 1)) →
    (∀ g ∈ unitaryCompact ℝ (r + 1), ∃ k, iK k = g) →
  ∀ (ds : List RealBlock) (a : ℝˣ) (μ : Measure K), μ.IsHaarMeasure →
  ∀ (κ : K → ℂ), Continuous κ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k))) →
  ∀ (f : Automorphic.realStandardKFinite n ds)
    (B : Automorphic.realStandardKFinite n ds →ₗ[ℂ] (G → ℂ)),
    IsRealUniformWhittakerIntertwiner r ds a B →
  ∀ (p : G → Automorphic.realStandardKFinite n ds),
    (∀ (g : G) (x : K), (p g : G → ℂ) (iK x) =
      ∫ k, κ k * (f : G → ℂ) (iK x * iK k * g) ∂μ) →
    (∀ x g : G, B (p g) x = ∫ k, κ k * B f (x * iK k * g) ∂μ) →
    ∃ (m : ℕ) (W : Fin m → G → ℂ) (κ' : Fin m → K → ℂ),
      (∀ j, W j ∈ realUniformWhittakerModel r ds a ∧ Continuous (κ' j)) ∧
      ∀ x g : G,
        (∫ k, κ k * B f (x * iK k * g) ∂μ) =
          ∑ j, W j x * (∫ k, κ' j k * (f : G → ℂ) (iK k * g) ∂μ) ∧
        (∫ k, κ k * wd (B f) (x * iK k * g) ∂μ) =
          ∑ j, wd (W j) x * (∫ k, κ' j k * (f : G → ℂ) (iK k * ι g) ∂μ)

theorem realLocalCompactProjectionReduction :
    RealLocalCompactProjectionReductionStatement (K := K) r := by
  intro iK hiK hmem hsurj ds a μ hμ κ hκ hκfin f B hB p hp hProj
  let : μ.IsHaarMeasure := hμ
  let E := Automorphic.realStandardKFinite n ds
  let ρ : E →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun v k => (v : G → ℂ) (iK k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := by
    intro v v' hv
    apply Subtype.ext
    refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries v.2.1.1 v'.2.1.1 fun g hg => ?_
    obtain ⟨k, rfl⟩ := hsurj g hg
    exact congrFun hv k
  have hf : Continuous (f : G → ℂ) := f.2.1.1.1.continuous
  have hfK (g : G) : Continuous (fun k : K => (f : G → ℂ) (iK k * g)) :=
    hf.comp (hiK.mul continuous_const)
  obtain ⟨m, v, κ', hκ', hv⟩ :=
    exists_compactPairing_expansion μ iK f hfK κ hκ
      (hasFiniteCompactConvolutionKernel_of_finite_translates κ hκ hκfin) ρ hρ p hp
  let W := fun j => B (v j)
  have hp' (x g : G) : (∫ k, κ k * B f (x * iK k * g) ∂μ) =
      ∑ j, W j x * (∫ k, κ' j k * (f : G → ℂ) (iK k * g) ∂μ) := by
    rw [← hProj, hv, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, W]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨m, W, κ', ?_, fun x g => ⟨hp' x g, ?_⟩⟩
  · intro j
    exact ⟨Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v j, rfl⟩), hκ' j⟩
  · let wx := GeneralLinear.weylLong n ℝ * ι x
    have hi (k : K) : wd (B f) (x * iK k * g) = B f (wx * iK k * ι g) := by
      simp only [ArchimedeanLocal.dualFunction, wx, map_mul, inverseTranspose_orthogonal (hmem k),
        mul_assoc]
    have hi' (j : Fin m) : wd (W j) x = W j wx := rfl
    simp_rw [hi, hi']
    exact hp' wx (ι g)

/-! ### Compact pairings on the smooth principal series -/

variable (r) in
/-- The pairing of a smooth principal-series vector with a continuous weight on a compact
group mapping to the general linear group. -/
def compactPairing (χ : ℕ → ℝˣ → ℂ) (iK : K →* G) (hiK : Continuous iK) (μ : Measure K)
    [IsFiniteMeasure μ] (w : K → ℂ) (hw : Continuous w) : principalSeries ℝ n χ →ₗ[ℂ] ℂ where
  toFun φ := ∫ k, w k * (φ : G → ℂ) (iK k) ∂μ
  map_add' φ ψ := by
    have hφ : Continuous fun k : K => (φ : G → ℂ) (iK k) := φ.2.1.continuous.comp hiK
    have hψ : Continuous fun k : K => (ψ : G → ℂ) (iK k) := ψ.2.1.continuous.comp hiK
    have h1 : Integrable (fun k : K => w k * (φ : G → ℂ) (iK k)) μ :=
      (hw.mul hφ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h2 : Integrable (fun k : K => w k * (ψ : G → ℂ) (iK k)) μ :=
      (hw.mul hψ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_add h1 h2]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    change w k * ((φ : G → ℂ) (iK k) + (ψ : G → ℂ) (iK k)) = _
    ring
  map_smul' c φ := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    change w k * (c * (φ : G → ℂ) (iK k)) = c * (w k * (φ : G → ℂ) (iK k))
    ring

omit [IsTopologicalGroup K] in
theorem compactPairing_apply (χ : ℕ → ℝˣ → ℂ) (iK : K →* G) (hiK : Continuous iK)
    (μ : Measure K) [IsFiniteMeasure μ] (w : K → ℂ) (hw : Continuous w)
    (φ : principalSeries ℝ n χ) :
    compactPairing r χ iK hiK μ w hw φ = ∫ k, w k * (φ : G → ℂ) (iK k) ∂μ :=
  rfl

omit [IsTopologicalGroup K] in
/-- A compact pairing over a compact group mapping into the orthogonal group has a compact
derivative bound of order zero. -/
theorem hasCompactDerivativeBound_compactPairing (ds : List RealBlock) (iK : K →* G)
    (hiK : Continuous iK) (hmem : ∀ k, iK k ∈ unitaryCompact ℝ (r + 1)) (μ : Measure K)
    [IsFiniteMeasure μ] (w : K → ℂ) (hw : Continuous w) :
    RealPrincipalSeries.HasCompactDerivativeBound r ds
      (compactPairing r (realPositionCharacter ds) iK hiK μ w hw) := by
  refine ⟨1, fun _ => [], ∫ k, ‖w k‖ ∂μ, integral_nonneg fun _ => norm_nonneg _, ?_⟩
  intro φ B hB
  have hb (k : K) : ‖(φ : G → ℂ) (iK k)‖ ≤ B 0 := hB 0 (iK k) (hmem k)
  rw [compactPairing_apply, Fin.sum_univ_one]
  calc
    ‖∫ k, w k * (φ : G → ℂ) (iK k) ∂μ‖ ≤ ∫ k, ‖w k * (φ : G → ℂ) (iK k)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ k, ‖w k‖ * B 0 ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((hw.norm.mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (ae_of_all _ fun k => ?_)
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _)
    _ = (∫ k, ‖w k‖ ∂μ) * B 0 := integral_mul_const _ _

omit [IsTopologicalGroup K] in
/-- The compact pairing of a right translate of an included standard vector is the compact
integral of the vector. -/
theorem compactPairing_translate (ds : List RealBlock) (iK : K →* G) (hiK : Continuous iK)
    (μ : Measure K) [IsFiniteMeasure μ] (w : K → ℂ) (hw : Continuous w)
    (f : Automorphic.realStandardKFinite n ds) (g : G) :
    compactPairing r (realPositionCharacter (RealPrincipalSeries.expand ds)) iK hiK μ w hw
        (RealPrincipalSeries.translate r (RealPrincipalSeries.expand ds) g
          (RealPrincipalSeries.expandedSmoothInclusion r ds f)) =
      ∫ k, w k * (f : G → ℂ) (iK k * g) ∂μ :=
  rfl

end Compact

end Langlands.Global.RankinSelbergGlobal.RealJacquet
