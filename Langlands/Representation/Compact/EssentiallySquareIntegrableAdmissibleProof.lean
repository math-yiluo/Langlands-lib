import Langlands.Representation.Compact.UnitarySquareIntegrableStatements
import Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Renard IV.3.2: admissibility of essentially square-integrable representations -/

noncomputable section

open MeasureTheory Langlands.Hecke

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- A left-compact-open-invariant L2 function is bounded. -/
theorem bounded_sq_of_left_invariant
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : OpenSubgroup Q) (hH : IsCompact (H : Set Q)) (f : Q → ℝ) (hf : MemLp f 2 μ)
    (hinv : ∀ (h : H) (q : Q), f ((h : Q) * q) = f q) :
    ∃ C : ℝ, ∀ q, (f q) ^ 2 ≤ C := by
  have hmass : 0 < μ.real (H : Set Q) := by
    apply ENNReal.toReal_pos
    · exact H.isOpen.measure_ne_zero μ ⟨1, H.one_mem⟩
    · exact hH.measure_lt_top.ne
  refine ⟨(∫ q, (f q) ^ 2 ∂μ) / μ.real (H : Set Q), fun q => ?_⟩
  apply (le_div_iff₀ hmass).mpr
  have hint := hf.integrable_sq.comp_mul_right q
  have hle := integral_mono_measure (μ := μ.restrict (H : Set Q)) (ν := μ) Measure.restrict_le_self
    (Filter.Eventually.of_forall fun z : Q => sq_nonneg (f (z * q))) hint
  have heq : (∫ z in (H : Set Q), (f (z * q)) ^ 2 ∂μ) =
      μ.real (H : Set Q) * (f q) ^ 2 := by
    rw [setIntegral_congr_fun H.isOpen.measurableSet (fun z hz => by rw [hinv ⟨z, hz⟩ q]),
      setIntegral_const, smul_eq_mul]
  rw [heq] at hle
  have htrans := integral_mul_right_eq_self (μ := μ) (fun z => (f z) ^ 2) q
  change (∫ z, (f (z * q)) ^ 2 ∂μ) = _ at htrans
  rw [htrans] at hle
  simpa only [mul_comm] using hle

section FixedSpace

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
  (c : UnitaryCentralCharacter ρ)
  (hL2 : ∀ (ℓ : SmoothDual ρ) (x : V), MemLp (c.coefficientNorm ℓ x) 2 μ)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

include c hL2 in
/-- Square integrability bounds every fixed-level coefficient. -/
theorem fixed_coefficient_bounded (Φ : Module.Dual ℂ (fixedVectors ρ K.toSubgroup)) (x : V) :
    ∃ C : ℝ, ∀ g : G,
      ‖CompactCoefficientClass.fixedExtension ν ρ hs K hK Φ (ρ g x)‖ ^ 2 ≤ C := by
  let Λ := CompactCoefficientClass.fixedExtension ν ρ hs K hK Φ
  let ℓ : SmoothDual ρ := ⟨Λ, CompactCoefficientClass.fixedExtension_isSmoothVector ν ρ hs K hK Φ⟩
  let H : OpenSubgroup (G ⧸ Subgroup.center G) :=
    { toSubgroup := K.toSubgroup.map (QuotientGroup.mk' (Subgroup.center G))
      isOpen' := QuotientGroup.isOpenMap_coe _ K.isOpen }
  have hH : IsCompact (H : Set (G ⧸ Subgroup.center G)) :=
    hK.image QuotientGroup.continuous_mk
  have hinv : ∀ (h : H) (q : G ⧸ Subgroup.center G),
      c.coefficientNorm ℓ x ((h : G ⧸ Subgroup.center G) * q) = c.coefficientNorm ℓ x q := by
    intro h q
    obtain ⟨k, hk, heq⟩ := h.property
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← heq]
    change c.coefficientNorm ℓ x (QuotientGroup.mk k * QuotientGroup.mk g) = _
    rw [← QuotientGroup.mk_mul, c.coefficientNorm_mk, c.coefficientNorm_mk]
    change ‖Λ (ρ (k * g) x)‖ = ‖Λ (ρ g x)‖
    rw [map_mul, Module.End.mul_apply]
    congr 1
    exact CompactCoefficientClass.dualAverage_apply_rho ν ρ hs K hK _ hk (ρ g x)
  obtain ⟨C, hC⟩ := bounded_sq_of_left_invariant μ H hH (c.coefficientNorm ℓ x) (hL2 ℓ x) hinv
  exact ⟨C, fun g => hC (QuotientGroup.mk g)⟩

include ν hs hK hi c hL2 in
/-- Irreducibility and L2 coefficients make every compact-open fixed space finite. -/
theorem finite_fixedVectors_of_squareIntegrable :
    Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := by
  classical
  by_cases h0 : fixedVectors ρ K.toSubgroup = ⊥
  · rw [h0]
    infer_instance
  obtain ⟨ξ, hξK, hξ0⟩ := (Submodule.ne_bot_iff _).mp h0
  let P := fixedProjection ν ρ hs K hK
  let u : G → fixedVectors ρ K.toSubgroup := fun g => P (ρ g ξ)
  have hspan : Submodule.span ℂ (Set.range u) = ⊤ := by
    have hrange : Set.range u = P '' Set.range (fun g => ρ g ξ) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_range_orbit_eq_top hi hξ0, Submodule.map_top,
      LinearMap.range_eq_top]
    intro y
    exact ⟨y, fixedProjection_fixed ν ρ hs K hK y⟩
  obtain ⟨b, hbu, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range u)
  let B : Module.Basis b ℂ (fixedVectors ρ K.toSubgroup) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  have hbfin : Finite b := by
    by_contra hb
    let : Infinite b := not_finite_iff_infinite.mp hb
    let e := Infinite.natEmbedding b
    let a : b → ℂ := Function.extend e (fun n : ℕ => (n : ℂ)) (fun _ => 0)
    let Φ : Module.Dual ℂ (fixedVectors ρ K.toSubgroup) := B.constr ℂ a
    obtain ⟨C, hC⟩ := fixed_coefficient_bounded ν μ ρ hs c hL2 K hK Φ ξ
    obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
    obtain ⟨g, hg⟩ := hbu (e n).property
    have hval : Φ (u g) = (n : ℂ) := by
      have hB : B (e n) = u g := by
        simpa only [B, Module.Basis.mk_apply] using hg.symm
      rw [← hB]
      exact (B.constr_basis ℂ a (e n)).trans (e.injective.extend_apply _ _ n)
    have hbound := hC g
    rw [CompactCoefficientClass.fixedExtension_apply] at hbound
    change ‖Φ (u g)‖ ^ 2 ≤ C at hbound
    rw [hval, Complex.norm_natCast] at hbound
    have h1 : (1 : ℝ) < n := (le_max_right C 1).trans_lt hn
    have hCn : C < n := (le_max_left C 1).trans_lt hn
    nlinarith
  let := hbfin
  exact Module.Finite.of_basis B

end FixedSpace

/-- Renard IV.3.2 Proposition, including arbitrary smooth character twists. -/
theorem essentiallySquareIntegrableAdmissible : EssentiallySquareIntegrableAdmissibleStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ π hi ω hω hsq
  obtain ⟨c, hc⟩ := hsq
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haar
  have hadm : (π.twist ω hω).IsAdmissible := by
    refine ⟨(π.twist ω hω).isSmooth, fun K => ?_⟩
    obtain ⟨L, hL, hLK⟩ := hcof K
    have := finite_fixedVectors_of_squareIntegrable ν μ (π.twist ω hω).representation
      (π.twist ω hω).isSmooth ((SmoothRep.isIrreducible_twist_iff ω hω π).mpr hi) c hc L hL
    exact finite_fixedVectors_of_le hLK
  exact (SmoothRep.isAdmissible_twist_iff ω hω π).mp hadm

end Langlands.Renard.CompactRepresentation
