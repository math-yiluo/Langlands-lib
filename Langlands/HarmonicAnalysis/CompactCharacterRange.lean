import Langlands.HarmonicAnalysis.CompactCharacterCompleteness
import Mathlib.Topology.UrysohnsLemma

/-! # Surjectivity detected by a separating character family -/

noncomputable section

open MeasureTheory Set Submodule

universe u v

namespace Langlands.HarmonicAnalysis.CompactCharacterRange

open CompactCharacterCompleteness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type v} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]

/-- Averaging a function along a translated compact-group homomorphism. -/
def average [CompactSpace G] [CompactSpace X]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    (f : G →ₜ* X) (s : X) : C(X, ℂ) →L[ℂ] ℂ := by
  have hint (p : C(X, ℂ)) : Integrable (fun g => p (s * f g)) μ := by
    refine Integrable.of_bound
      (p.continuous.comp (continuous_const.mul f.continuous)).aestronglyMeasurable
      ‖p‖ (ae_of_all _ fun g => p.norm_coe_le_norm _)
  let L : C(X, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ g, p (s * f g) ∂μ
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint p) (hint q)
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  exact L.mkContinuous 1 fun p => by
    calc
      ‖L p‖ ≤ ‖p‖ * μ.real univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun g => p.norm_coe_le_norm _)
      _ = 1 * ‖p‖ := by simp

/-- A compact image fills the target if pullback kills no nontrivial member of a
separating character subgroup. -/
theorem surjective_of_character_detection [CompactSpace G] [T2Space G]
    [CompactSpace X] [T2Space X]
    (f : G →ₜ* X) (H : Subgroup (PontryaginDual X))
    (hsep : ∀ x y : X, x ≠ y →
      ∃ χ : H, (χ : PontryaginDual X) x ≠ (χ : PontryaginDual X) y)
    (hfaith : ∀ χ ∈ H, (χ.comp f : PontryaginDual G) = 1 → χ = 1) :
    Function.Surjective f := by
  classical
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ := ⟨by simpa [μ] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G)))⟩
  intro t
  by_contra ht
  have hcompact : IsCompact (range f) := isCompact_range f.continuous
  have hcompact' : IsCompact (range (fun g => t * f g)) :=
    isCompact_range (continuous_const.mul f.continuous)
  have hdis : Disjoint (range f) (range (fun g => t * f g)) := by
    apply disjoint_left.mpr
    rintro _ ⟨g, rfl⟩ ⟨h, he⟩
    apply ht
    refine ⟨g / h, ?_⟩
    rw [map_div]
    exact (div_eq_iff_eq_mul).mpr he.symm
  obtain ⟨p, hp0, hp1, _⟩ := exists_continuous_zero_one_of_isClosed
    hcompact.isClosed hcompact'.isClosed hdis
  let q : C(X, ℂ) := ⟨fun x => (p x : ℂ), Complex.continuous_ofReal.comp p.continuous⟩
  let L := average μ f t - average μ f 1
  have hspan : span ℂ (range (fun η : H => complexMap (η : PontryaginDual X))) ≤
      LinearMap.ker (L : _ →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨η, rfl⟩
    change average μ f t (complexMap (η : PontryaginDual X)) -
      average μ f 1 (complexMap (η : PontryaginDual X)) = 0
    by_cases he : (η : PontryaginDual X) = 1
    · simp [he, average, complexMap]
    · have hz := integral_eq_zero μ ((η : PontryaginDual X).comp f)
        (fun h => he (hfaith η η.property h))
      change (∫ g, ((η : PontryaginDual X) (f g) : ℂ) ∂μ) = 0 at hz
      change (∫ g, ((η : PontryaginDual X) (t * f g) : ℂ) ∂μ) -
        (∫ g, ((η : PontryaginDual X) (1 * f g) : ℂ) ∂μ) = 0
      simp only [map_mul, Circle.coe_mul, one_mul, integral_const_mul, hz, mul_zero,
        sub_self]
  have hker := Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [span_topologicalClosure_eq_top H hsep] at hker
  have hz : L q = 0 := hker Submodule.mem_top
  have heval : L q = 1 := by
    change (∫ g, (p (t * f g) : ℂ) ∂μ) - (∫ g, (p (1 * f g) : ℂ) ∂μ) = 1
    have h0 (g : G) : p (f g) = 0 := hp0 (mem_range_self g)
    have h1 (g : G) : p (t * f g) = 1 := hp1 (mem_range_self g)
    simp [h0, h1]
  exact one_ne_zero (heval.symm.trans hz)

end Langlands.HarmonicAnalysis.CompactCharacterRange
