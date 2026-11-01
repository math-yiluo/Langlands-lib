import Langlands.Global.ArchimedeanJointFiniteAnalyticityStatement
import Langlands.Global.ArchimedeanCartanPolynomialProof
import Langlands.Global.ArchimedeanCartanPolynomialRealization
import Langlands.Analysis.ScalarEllipticAnalyticityProof

/-! # Real analyticity of genuinely joint finite smooth functions -/

noncomputable section
universe u
open scoped Classical ContDiff Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Genuine joint central and compact differential finiteness implies real
analyticity at every actual archimedean unit. -/
theorem jointFiniteAnalyticity
    (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    JointFiniteAnalyticityStatement K n := by
  intro f hf
  obtain ⟨p, hp, _hdegree, hann⟩ :=
    cartanSquareSumPolynomialAnnihilation K n f hf
  obtain ⟨d, D, hcoeff, haction, hsymbol⟩ :=
    cartanPolynomialCoordinateRealization K n p hp
  let S : Set (ArchimedeanMatrix K n) :=
    Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)
  have hS : IsOpen S := Units.isOpenEmbedding_val.isOpen_range
  have hsm : ContDiffOn ℝ ∞ (coordinateExtension K n f) S :=
    coordinateExtension_contDiffOn K n f
  have hell : D.IsEllipticOn S := by
    rintro x ⟨g, rfl⟩ ξ hξ
    rw [hsymbol g ξ]
    apply pow_ne_zero
    exact_mod_cast (ne_of_gt (ambientCartanCovectorForm_unit_pos K n g ξ hξ))
  have heqn : ∀ x ∈ S, D.action (coordinateExtension K n f) x = 0 := by
    rintro x ⟨g, rfl⟩
    rw [haction _ hsm g, cartanAmbientPolynomial_coordinateExtension,
      hann f (self_mem_jointOrbitSpan K n f)]
    rfl
  have hanalytic : AnalyticOnNhd ℝ (coordinateExtension K n f) S :=
    Langlands.Analysis.scalarEllipticAnalyticity
      (ArchimedeanMatrix K n) d (2 * p.natDegree)
      D S (coordinateExtension K n f) hS hcoeff hell hsm heqn
  intro g
  exact hanalytic (g : ArchimedeanMatrix K n) ⟨g, rfl⟩

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    JointFiniteAnalyticityStatement K n :=
  @jointFiniteAnalyticity

example (K : Type u) [Field K] [NumberField K] :
    JointFiniteAnalyticityStatement K 0 :=
  jointFiniteAnalyticity K 0

end Langlands.Global.ArchimedeanGL
