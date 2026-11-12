import Langlands.Representation.CompactCoefficient.CompactFormalDegreeStatements
import Langlands.Representation.CompactCoefficient.AdmissibleLifting
import Langlands.Representation.Smooth.SmallRealizationProof
import Mathlib.LinearAlgebra.Trace

noncomputable section

universe u v

open MeasureTheory
open scoped BigOperators

namespace Langlands.Renard.CompactRepresentation

open CompactSplitting

section Compact

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

include hρ in
/-- A nonzero vector in an irreducible smooth representation of a compact
group has a finite spanning orbit. -/
theorem finiteDimensional_of_compact_smooth_irreducible (hi : ρ.IsIrreducible) :
    FiniteDimensional ℂ V := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  let K : OpenSubgroup G := ⊤
  have hK : IsCompact (K : Set G) := isCompact_univ
  let : Finite (Compact.orbit (ρ.comp K.toSubgroup.subtype) a) :=
    Compact.finite_orbit_of_smooth ρ hρ K hK a
  have hset : Set.range (fun g : G => ρ g a) =
      Compact.orbit (ρ.comp K.toSubgroup.subtype) a := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.val, rfl⟩
  have hf : (Set.range (fun g : G => ρ g a)).Finite := by
    rw [hset]
    exact Set.toFinite _
  have : FiniteDimensional ℂ (⊤ : Submodule ℂ V) := by
    rw [← span_range_orbit_eq_top hi ha]
    exact FiniteDimensional.span_of_finite ℂ hf
  exact Module.Finite.of_surjective
    (Submodule.topEquiv : (⊤ : Submodule ℂ V) ≃ₗ[ℂ] V).toLinearMap
    (Submodule.topEquiv : (⊤ : Submodule ℂ V) ≃ₗ[ℂ] V).surjective

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
variable (hc : HasCompactSmoothDualCoefficients ρ)

/-- On a compact group of mass one, the trace of the coefficient integral
intertwiner is evaluation of the functional at its input vector. -/
theorem trace_coefficientLift [FiniteDimensional ℂ V]
    (ℓ : SmoothDual ρ) (x : V) :
    LinearMap.trace ℂ V
      (liftMap μ ρ hρ hc ℓ.val ℓ.property ρ hρ x).toLinearMap = ℓ.val x := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (∑ i, b.coord i (Hecke.integratedAction μ ρ hρ
    (testMap ρ hρ hc ℓ.val ℓ.property (b i)) x)) = ℓ.val x
  simp_rw [Hecke.integratedAction_dual]
  change (∑ i, ∫ g, ℓ.val (ρ g⁻¹ (b i)) * b.coord i (ρ g x) ∂μ) = ℓ.val x
  have hint (i : Fin (Module.finrank ℂ V)) :
      Integrable (fun g : G => ℓ.val (ρ g⁻¹ (b i)) * b.coord i (ρ g x)) μ := by
    apply Continuous.integrable_of_hasCompactSupport
      ((invCoeff_continuous ρ hρ ℓ.val (b i)).mul
        (((Hecke.orbitMap_locallyConstant ρ (hρ x)).comp (b.coord i)).continuous))
    exact HasCompactSupport.of_compactSpace _
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i)]
  have hsum (g : G) :
      (∑ i, ℓ.val (ρ g⁻¹ (b i)) * b.coord i (ρ g x)) = ℓ.val x := by
    calc
      _ = ℓ.val (ρ g⁻¹ (∑ i, b.repr (ρ g x) i • b i)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = ℓ.val x := by rw [b.sum_repr, Representation.inv_self_apply]
  simp_rw [hsum]
  simp

/-- The compact probability-measure coefficient formula follows from Schur
and the trace computation. -/
theorem compact_coefficientAction [FiniteDimensional ℂ V] (hi : ρ.IsIrreducible)
    (ℓ : SmoothDual ρ) (x a : V) :
    Hecke.integratedAction μ ρ hρ (testMap ρ hρ hc ℓ.val ℓ.property a) x =
      ((Module.finrank ℂ V : ℂ)⁻¹ * ℓ.val x) • a := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have ha : IsAdmissible ρ := ⟨hρ, fun _ => inferInstance⟩
  let T := liftMap μ ρ hρ hc ℓ.val ℓ.property ρ hρ x
  obtain ⟨c, hcT, -⟩ := admissibleSchur_scalarEndomorphism ρ ha hi T
  have htrace := trace_coefficientLift ρ hρ μ hc ℓ x
  change LinearMap.trace ℂ V T.toLinearMap = ℓ.val x at htrace
  rw [hcT] at htrace
  change LinearMap.trace ℂ V (c • (1 : Module.End ℂ V)) = ℓ.val x at htrace
  rw [map_smul, LinearMap.trace_one, smul_eq_mul] at htrace
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hceq : c = (Module.finrank ℂ V : ℂ)⁻¹ * ℓ.val x := by
    apply (mul_left_cancel₀ hd)
    rw [mul_inv_cancel_left₀ hd]
    exact (mul_comm _ _).trans htrace
  change T a = _
  rw [hcT, hceq]
  rfl

end Compact

/-- Renard IV.1.4, Remark 2: the formal degree for a compact group of Haar
mass one is its dimension. -/
theorem compactGroupFormalDegree : CompactGroupFormalDegreeStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ τ hμ hi
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  have hfinite := finiteDimensional_of_compact_smooth_irreducible τ.representation τ.isSmooth hi
  let := hfinite
  have hc : HasCompactSmoothDualCoefficients τ.representation :=
    fun _ _ _ => HasCompactSupport.of_compactSpace _
  refine ⟨hfinite, ?_⟩
  intro a ℓ f hf x
  have htest : Hecke.HeckeAlgebra.toTestFunction μ f =
      testMap τ.representation τ.isSmooth hc ℓ.val ℓ.property a := by
    ext g
    exact hf g
  change Hecke.integratedAction μ τ.representation τ.isSmooth
    (Hecke.HeckeAlgebra.toTestFunction μ f) x = _
  rw [htest]
  exact compact_coefficientAction τ.representation τ.isSmooth μ hc hi ℓ x a

end Langlands.Renard.CompactRepresentation
