import Langlands.Representation.GodementJacquet.WhittakerModelInclusion
import Langlands.Representation.Compact.OrbitMeanTranslation
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Finite coefficient separation of the normalized compact middle average
in JPSS Section 6.3, formula (7). No topology is placed on a module. -/

noncomputable section

namespace Langlands.Compact

open scoped BigOperators

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The finite-orbit compact average, restricted to its actual fixed-vector codomain. -/
def averageToFixed : V →ₗ[ℂ] fixedVectors ρ K.toSubgroup :=
  (averageMap ρ hρ.1 K hK).codRestrict (fixedVectors ρ K.toSubgroup)
    (averageMap_mem_fixedVectors ρ hρ.1 K hK)

/-- Translation by the averaging subgroup leaves the projection unchanged. -/
theorem averageToFixed_translate {k : G} (hk : k ∈ K) (v : V) :
    averageToFixed ρ hρ K hK (ρ k v) = averageToFixed ρ hρ K hK v := by
  apply Subtype.ext
  exact orbitMean_apply (ρ.comp K.toSubgroup.subtype) ⟨k, hk⟩ v

/-- A finite basis of the actual fixed-vector space, chosen before any input vector. -/
def fixedBasis : Module.Basis (Fin (Module.finrank ℂ (fixedVectors ρ K.toSubgroup)))
    ℂ (fixedVectors ρ K.toSubgroup) := by
  letI : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  exact Module.finBasis ℂ _

/-- Coordinates of the compact projection are actual smooth dual vectors. -/
def averageCoordinate (i : Fin (Module.finrank ℂ (fixedVectors ρ K.toSubgroup))) :
    SmoothDual ρ := by
  let Λ : Module.Dual ℂ V := (fixedBasis ρ hρ K).coord i |>.comp
    (averageToFixed ρ hρ K hK)
  refine ⟨Λ, K, ?_⟩
  intro k
  apply LinearMap.ext
  intro v
  change (fixedBasis ρ hρ K).coord i (averageToFixed ρ hρ K hK (ρ (k.val)⁻¹ v)) =
    (fixedBasis ρ hρ K).coord i (averageToFixed ρ hρ K hK v)
  rw [averageToFixed_translate ρ hρ K hK (K.inv_mem k.property)]

/-- The second-variable functions are actual bi-smooth coefficients. -/
def averageCoefficient (v : V)
    (i : Fin (Module.finrank ℂ (fixedVectors ρ K.toSubgroup))) :
    GodementJacquet.biSmoothMatrixCoefficients ρ :=
  ⟨GodementJacquet.biSmoothCoefficient ρ (averageCoordinate ρ hρ K hK i)
      ⟨v, hρ.1 v⟩, Submodule.subset_span ⟨_, _, rfl⟩⟩

/-- The fixed basis and its actual matrix coefficients expand every averaged translate. -/
theorem averageToFixed_expansion (v : V) (h : G) :
    (averageToFixed ρ hρ K hK (ρ h v)).val =
      ∑ i, (averageCoefficient ρ hρ K hK v i).val h • (fixedBasis ρ hρ K i).val := by
  have hb := congrArg (fun w : fixedVectors ρ K.toSubgroup => w.val)
    ((fixedBasis ρ hρ K).sum_repr (averageToFixed ρ hρ K hK (ρ h v)))
  simpa only [averageCoefficient, GodementJacquet.biSmoothCoefficient_apply,
    averageCoordinate, LinearMap.comp_apply, Module.Basis.coord_apply,
    Submodule.coe_sum, Submodule.coe_smul] using hb.symm

/-- Finite separation of every averaged translate after any algebraic linear
functional. The fixed vectors are chosen before the input vector and functional. -/
theorem finiteAverageCoefficients :
    ∃ (m : ℕ) (B : Fin m → V), ∀ v : V,
      ∃ f : Fin m → GodementJacquet.biSmoothMatrixCoefficients ρ,
        ∀ (Λ : Module.Dual ℂ V) (h : G),
          Λ (averageToFixed ρ hρ K hK (ρ h v)).val =
            ∑ i, Λ (B i) * (f i).val h := by
  refine ⟨_, fun i => (fixedBasis ρ hρ K i).val,
    fun v => ⟨fun i => averageCoefficient ρ hρ K hK v i, fun Λ h => ?_⟩⟩
  have he := congrArg Λ (averageToFixed_expansion ρ hρ K hK v h)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using he

end Langlands.Compact

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance compactCoefficientsTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance compactCoefficientsValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance compactCoefficientsLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance compactCoefficientsMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance compactCoefficientsBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

set_option maxHeartbeats 1000000 in
/-- Exact finite separation of the normalized middle compact average, in the
specified original coefficient model and its actual bi-smooth coefficient module. -/
theorem adjacentRankCompact_middleAverage
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (r + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier))) :
    ∃ (m : ℕ) (B : Fin m → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin m → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          ∀ (g h : Langlands.GeneralLinear (r + 1) F.Carrier),
            ((generalLinearHaar F.Carrier r).real (K : Set _) : ℂ)⁻¹ *
                (∫ k in (K : Set _), glModelFunction ψ r σ ℓ W (g * k * h)
                  ∂generalLinearHaar F.Carrier r) =
              ∑ i : Fin m, glModelFunction ψ r σ ℓ (B i) g * (f i).val h := by
  let hadm : IsAdmissible (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ) :=
    GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hσ
  obtain ⟨m, B, hB⟩ := Compact.finiteAverageCoefficients
    (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (glModelRepresentation ψ r σ ℓ) hadm K hK
  refine ⟨m, B, fun W => ?_⟩
  obtain ⟨f, hf⟩ := hB W
  refine ⟨f, fun g h => ?_⟩
  let P := Compact.averageToFixed (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (glModelRepresentation ψ r σ ℓ) hadm K hK
  let A := GodementJacquet.Padic.modelPointAverage F ψ σ hσ.1 ℓ K hK g
  let mass : ℂ := (generalLinearHaar F.Carrier r).real (K : Set _)
  have hA : A (glModelRepresentation ψ r σ ℓ h W) = mass *
      glModelFunction ψ r σ ℓ (P (glModelRepresentation ψ r σ ℓ h W)).val g := by
    calc
      A (glModelRepresentation ψ r σ ℓ h W) =
          A (P (glModelRepresentation ψ r σ ℓ h W)).val := by
        exact (GodementJacquet.apply_averageMap_of_invariant
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ)
          hadm.1 K hK A
          (fun k hk v => GodementJacquet.Padic.modelPointAverage_invariant F ψ σ hσ.1 ℓ
            K hK g hk v) (glModelRepresentation ψ r σ ℓ h W)).symm
      _ = mass * glModelFunction ψ r σ ℓ
          (P (glModelRepresentation ψ r σ ℓ h W)).val g :=
        GodementJacquet.Padic.modelPointAverage_of_mem_fixedVectors F ψ σ hσ.1 ℓ
          K hK g (P (glModelRepresentation ψ r σ ℓ h W)).property
  have hmiddle : (∫ k in (K : Set _), glModelFunction ψ r σ ℓ W (g * k * h)
      ∂generalLinearHaar F.Carrier r) =
      mass * glModelFunction ψ r σ ℓ
        (P (glModelRepresentation ψ r σ ℓ h W)).val g := by
    simpa only [A, GodementJacquet.Padic.modelPointAverage_apply, glModelFunction_translate,
      mul_assoc] using hA
  rw [hmiddle, ← mul_assoc,
    inv_mul_cancel₀ (GodementJacquet.Padic.measureReal_openSubgroup_ne_zero F K hK), one_mul]
  let ev : (glCoefficientModel ψ r σ ℓ).toSubmodule →ₗ[ℂ] ℂ :=
    { toFun := fun w => glModelFunction ψ r σ ℓ w g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact hf ev h

end Langlands.RankinSelberg.Padic
