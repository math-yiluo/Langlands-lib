import Langlands.LocalFactor.Ramification.Herbrand.TruncationQuotientStatement
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof

/-!
# Truncation preserves the Weil degree

If the absolute upper group `G_F^μ` with `μ ≥ 0` acts transitively on the
`F`-embeddings of a finite extension `E`, the relative residue degree of the
prescribed inclusion `F → E` is one, so the inclusion of Weil groups
`W_E → W_F` preserves the geometric degree.
-/

noncomputable section

namespace Langlands.Ramification.Kummer

open LocalClassField HerbrandBridge Weil.Local
open _root_.Langlands.Ramification.Padic

universe u

variable {p : ℕ} [Fact p.Prime]

/-- If `E.field.fixingSubgroup ⊔ G_F^μ = ⊤` with `μ ≥ 0`, the relative residue
degree of the prescribed inclusion `F → E` is one. A geometric Frobenius lift of
`W_F` is moved by an inertia element into the image of `W_E`, so its degree `1`
is a multiple of the residue degree. -/
theorem extensionResidueDegree_eq_one_of_sup_upper_eq_top (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ)
    (hsup : E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤)
    (hμ : 0 ≤ μ) :
    extensionResidueDegree F (E.asPadicField (p := p)) (intermediateEmbedding F E) = 1 := by
  let w₀ : localWeilGroup F := localGeometricFrobenius F
  have hmem : localProjection F w₀ ∈
      E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, h, hh, hgh⟩ :=
    (Subgroup.mem_sup_of_normal_right (ht := absoluteUpperRamificationGroup_normal F μ)).mp hmem
  have hinert : h ∈ F.absoluteInertia F.canonicalTopologicalData := by
    rw [← absoluteUpperCanonicalInertia F]
    exact absoluteUpperRamificationGroup_antitone F hμ hh
  have hker : localResidueDegree F h = 1 := by
    rw [← localResidueDegree_ker F] at hinert
    exact hinert
  have hpair : localResidueDegree F g = Weil.frobenius (localDegree F w₀) := by
    have hw : localResidueDegree F (localProjection F w₀) =
        Weil.frobenius (localDegree F w₀) := w₀.property
    rw [← hgh, map_mul, hker, mul_one] at hw
    exact hw
  let w₁ : localWeilGroup F := ⟨(g, localDegree F w₀), hpair⟩
  have hw₁ : w₁ ∈ pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) := hg
  have hdeg := intermediateWeilEquiv_symm_degree F E ⟨w₁, hw₁⟩
  have h1 : localDegreeInt F w₁ = 1 := by
    change (localDegree F w₀).toAdd = 1
    rw [localGeometricFrobenius_degree]
    rfl
  change localDegreeInt F w₁ = _ at hdeg
  rw [h1] at hdeg
  have hnn : (0 : ℤ) ≤
      (extensionResidueDegree F (E.asPadicField (p := p)) (intermediateEmbedding F E) : ℤ) :=
    Int.natCast_nonneg _
  exact_mod_cast Int.eq_one_of_mul_eq_one_right hnn hdeg.symm

/-- **Truncation and unramified twists.** If an upper group `G_F^μ` with `μ ≥ 0`
acts transitively on the `F`-embeddings of `E`, the Weil inclusion `W_E → W_F`
preserves the geometric degree. -/
theorem truncationWeilDegree : TruncationWeilDegreeStatement.{u} := by
  intro p _ F E μ hsup hμ w
  rw [localDegree_intermediateWeilMap,
    extensionResidueDegree_eq_one_of_sup_upper_eq_top F E μ hsup hμ, pow_one]

end Langlands.Ramification.Kummer
