import Langlands.LocalFactor.UnitaryEuler
import Langlands.LocalFactor.WeilDeligne
import Langlands.Weil.Representation.UnitaryProof

/-!
# Unitary regularity for actual Weil--Deligne Euler operators

Positive forms are pulled back through the published inclusions of invariants
and monodromy kernels. The operator remains the actual group action.
-/

noncomputable section

universe uG uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- Restrict a positive form through the actual inclusion of normal-subgroup
invariants. -/
def invariantsInvariantPositiveForm (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (I : Subgroup G) [I.Normal] (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (invariants I A).representation :=
  b.comap (invariantsInclusion I A) Subtype.val_injective

/-- Normal-subgroup invariants of an actual unitary representation are unitary. -/
theorem isUnitary_invariants (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (I : Subgroup G) [I.Normal] (hA : IsUnitary A) : IsUnitary (invariants I A) := by
  obtain ⟨b⟩ := (isUnitary_iff_isUnitarizable A).mp hA
  exact (isUnitary_iff_isUnitarizable _).mpr ⟨invariantsInvariantPositiveForm A I b⟩

end Langlands.FiniteRepresentation

namespace Langlands.WeilDeligneRepresentation

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- Pull a positive form back through the actual monodromy-kernel inclusion. -/
def kernelInvariantPositiveForm (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm A.kernelRepresentation.representation :=
  b.comap A.kernelInclusion Subtype.val_injective

/-- The actual monodromy kernel of a unitary Weil representation is unitary. -/
theorem isUnitary_kernelRepresentation
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (hA : A.toFiniteRepresentation.IsUnitary) : A.kernelRepresentation.IsUnitary := by
  obtain ⟨b⟩ := (FiniteRepresentation.isUnitary_iff_isUnitarizable _).mp hA
  exact (FiniteRepresentation.isUnitary_iff_isUnitarizable _).mpr
    ⟨kernelInvariantPositiveForm A b⟩

/-- The actual inertia-fixed monodromy kernel inherits a chosen positive form. -/
def inertiaKernelInvariantPositiveForm
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (A.inertiaKernelRepresentation I).representation :=
  FiniteRepresentation.invariantsInvariantPositiveForm A.kernelRepresentation I
    (kernelInvariantPositiveForm A b)

/-- Unitarity descends to the actual inertia-fixed monodromy kernel. -/
theorem isUnitary_inertiaKernelRepresentation
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary) :
    (A.inertiaKernelRepresentation I).IsUnitary :=
  FiniteRepresentation.isUnitary_invariants _ I (isUnitary_kernelRepresentation A hA)

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.WeilDeligne

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- The actual inertia-kernel Euler denominator of a unitary parameter has no
zeros off the unit circle. -/
theorem eulerPolynomial_eval_ne_zero_of_isUnitary
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) {z : ℂ} (hz : ‖z‖ ≠ 1) : (eulerPolynomial A I g).eval z ≠ 0 := by
  obtain ⟨h, hh⟩ := A.isUnitary_inertiaKernelRepresentation I hA
  exact LocalFactor.eulerPolynomial_eval_ne_zero_of_preserves_positive_form
    (kernelOperator A I g) h (hh g) hz

/-- The actual spectral denominator of a unitary parameter is nonzero away from
the imaginary axis. -/
theorem eulerPolynomial_spectral_eval_ne_zero_of_isUnitary
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : s.re ≠ 0) :
    (eulerPolynomial A I g).eval
      (spectralParameter q (lt_trans zero_lt_one hq) s : ℂ) ≠ 0 :=
  eulerPolynomial_eval_ne_zero_of_isUnitary A I hA g
    (norm_spectralParameter_ne_one hq hs)

/-- Construct a regular spectral point for the actual inertia-fixed
monodromy-kernel operator of a unitary parameter. -/
def spectralRegularPointOfIsUnitary
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (hA : A.toFiniteRepresentation.IsUnitary)
    (g : G) (q : ℝ) (hq : 1 < q) (s : ℂ) (hs : s.re ≠ 0) :
    SpectralRegularPoint A I g q (lt_trans zero_lt_one hq) :=
  ⟨s, eulerPolynomial_spectral_eval_ne_zero_of_isUnitary A I hA g hq hs⟩

end Langlands.LocalFactor.WeilDeligne
