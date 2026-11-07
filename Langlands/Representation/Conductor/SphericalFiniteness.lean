import Langlands.Representation.Conductor.SphericalPolynomial
import Langlands.Representation.Conductor.Congruence
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Compact-modulo-unipotent finiteness of the spherical Laurent formula
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical
open Langlands.QuotientIntegration

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ} {ϖ : Fˣ}
variable (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ)

/-- The Laurent-valued spherical formula is locally constant when the character
is trivial on integral unipotent elements. -/
theorem sphericalWhittakerPolynomial_isLocallyConstant
    (hθ : Iwasawa.IsIntegrallyTrivial (ValuativeRel.valuation F) θ) :
    IsLocallyConstant (sphericalWhittakerPolynomial hϖ θ q) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  have hK : IsOpen (levelOpenSubgroup F n 0 : Set (Langlands.GeneralLinear (n + 1) F)) :=
    (levelOpenSubgroup F n 0).isOpen
  refine ⟨(fun h : Langlands.GeneralLinear (n + 1) F => g⁻¹ * h) ⁻¹'
      (levelOpenSubgroup F n 0 : Set (Langlands.GeneralLinear (n + 1) F)),
    hK.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ levelSubgroup F n 0
    rw [inv_mul_cancel]
    exact (levelSubgroup F n 0).one_mem
  · intro h hh
    have hk : g⁻¹ * h ∈ integralSubgroup (ValuativeRel.valuation F).integer n := by
      rw [← levelSubgroup_zero]
      exact hh
    have hr := sphericalWhittakerPolynomial_mul_integral hϖ θ q hθ g hk
    rwa [mul_inv_cancel_left] at hr

/-- On a compact set the Laurent formula takes only finitely many values. -/
theorem sphericalWhittakerPolynomial_finite_image
    (hθ : Iwasawa.IsIntegrallyTrivial (ValuativeRel.valuation F) θ)
    {C : Set (Langlands.GeneralLinear (n + 1) F)} (hC : IsCompact C) :
    (sphericalWhittakerPolynomial hϖ θ q '' C).Finite := by
  let : TopologicalSpace (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) := ⊥
  have : DiscreteTopology (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) := ⟨rfl⟩
  exact (hC.image (sphericalWhittakerPolynomial_isLocallyConstant hϖ θ q hθ).continuous
    ).finite_of_discrete

/-- The vector space spanned by spherical Laurent values on a set. -/
def sphericalWhittakerValueSpan (C : Set (Langlands.GeneralLinear (n + 1) F)) :
    Submodule ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :=
  Submodule.span ℂ (sphericalWhittakerPolynomial hϖ θ q '' C)

theorem sphericalWhittakerValueSpan_finite
    (hθ : Iwasawa.IsIntegrallyTrivial (ValuativeRel.valuation F) θ)
    {C : Set (Langlands.GeneralLinear (n + 1) F)} (hC : IsCompact C) :
    Module.Finite ℂ (sphericalWhittakerValueSpan hϖ θ q C) :=
  Module.Finite.span_of_finite ℂ (sphericalWhittakerPolynomial_finite_image hϖ θ q hθ hC)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Values on the unipotent saturation of a compact set lie in its finite
value span. -/
theorem sphericalWhittakerPolynomial_mem_valueSpan
    (hθ : Iwasawa.IsIntegrallyTrivial (ValuativeRel.valuation F) θ)
    {C : Set (Langlands.GeneralLinear (n + 1) F)}
    (u : upperUnipotent (n + 1) F) {c : Langlands.GeneralLinear (n + 1) F} (hc : c ∈ C) :
    sphericalWhittakerPolynomial hϖ θ q (u.val * c) ∈
      sphericalWhittakerValueSpan hϖ θ q C := by
  rw [sphericalWhittakerPolynomial_unipotent_mul hϖ θ q hθ]
  simpa only [Algebra.smul_def] using
    (sphericalWhittakerValueSpan hϖ θ q C).smul_mem (θ u : ℂ)
      (Submodule.subset_span (Set.mem_image_of_mem _ hc))

/-- Spherical Laurent values above a compact subset of the actual left
unipotent quotient belong to one finite-dimensional complex vector space. -/
theorem sphericalWhittakerPolynomial_finiteDimensional_on_quotientCompact
    (hθ : Iwasawa.IsIntegrallyTrivial (ValuativeRel.valuation F) θ)
    {D : Set (LeftQuotient (upperUnipotent (n + 1) F))} (hD : IsCompact D) :
    ∃ M : Submodule ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ),
      Module.Finite ℂ M ∧ ∀ g : Langlands.GeneralLinear (n + 1) F,
        leftQuotientMap (upperUnipotent (n + 1) F) g ∈ D →
          sphericalWhittakerPolynomial hϖ θ q g ∈ M := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : T2Space F := inferInstance
  have : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F))
  obtain ⟨C, hC, hCD⟩ := leftQuotient_exists_isCompact_image
    (upperUnipotent (n + 1) F) UpperUnipotent.isClosed hD
  refine ⟨sphericalWhittakerValueSpan hϖ θ q C,
    sphericalWhittakerValueSpan_finite hϖ θ q hθ hC, ?_⟩
  intro g hg
  rw [← hCD] at hg
  obtain ⟨c, hc, hcg⟩ := hg
  have hu : g * c⁻¹ ∈ upperUnipotent (n + 1) F :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hcg)
  have heq : (⟨g * c⁻¹, hu⟩ : upperUnipotent (n + 1) F).val * c = g := by simp
  rw [← heq]
  exact sphericalWhittakerPolynomial_mem_valueSpan hϖ θ q hθ _ hc

end Langlands.Conductor
