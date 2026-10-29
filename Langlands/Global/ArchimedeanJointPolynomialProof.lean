import Langlands.Global.ArchimedeanJointPolynomialStatement
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Polynomial annihilation on the actual finite joint orbit -/

noncomputable section
universe u v
open Polynomial
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

private theorem coe_aeval_restrict
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (L : Module.End ℂ V)
    (hL : ∀ x ∈ S, L x ∈ S) (p : Polynomial ℂ) (g : S) :
    ((aeval (L.restrict hL) p) g : V) = (aeval L p) g := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using
      (congrArg₂ (fun x y : V => x + y) hp hq)
  | monomial m c =>
    simp only [aeval_monomial, Module.End.mul_apply, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul_of_tower]
    rw [Module.End.pow_restrict m hL, LinearMap.coe_restrict_apply]

private theorem polynomial_annihilator_of_invariant
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) [Module.Finite ℂ S] (L : Module.End ℂ V)
    (hL : ∀ x ∈ S, L x ∈ S) :
    ∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = Module.finrank ℂ S ∧
      ∀ g : V, g ∈ S → (aeval L p) g = 0 := by
  let T : Module.End ℂ S := L.restrict hL
  refine ⟨T.charpoly, T.charpoly_monic, T.charpoly_natDegree, ?_⟩
  intro g hg
  have hzero := congrArg (fun A : Module.End ℂ S => (A ⟨g, hg⟩ : V))
    T.aeval_self_charpoly
  rw [coe_aeval_restrict] at hzero
  simpa only [LinearMap.zero_apply, Submodule.coe_zero] using hzero

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private theorem center_add_compact_preserves_jointOrbit
    (f : SmoothFunctions K n) (z : EnvelopingCenter K n)
    (b : compactEnvelopingSubalgebra K n) :
    ∀ g ∈ jointOrbitSpan K n f,
      envelopingAction K n (centerInclusion K n z + b.val) g ∈ jointOrbitSpan K n f := by
  intro g hg
  have hz := (jointOrbitSubrepresentation K n f).apply_mem_toSubmodule (z, 1) hg
  have hb := (jointOrbitSubrepresentation K n f).apply_mem_toSubmodule (1, b) hg
  change jointRepresentation K n (z, 1) g ∈ jointOrbitSpan K n f at hz
  change jointRepresentation K n (1, b) g ∈ jointOrbitSpan K n f at hb
  rw [jointRepresentation_center] at hz
  rw [jointRepresentation_compact] at hb
  change envelopingAction K n (centerInclusion K n z) g ∈ jointOrbitSpan K n f at hz
  change envelopingAction K n b.val g ∈ jointOrbitSpan K n f at hb
  simpa only [map_add, LinearMap.add_apply] using (jointOrbitSpan K n f).add_mem hz hb

/-- Cayley–Hamilton on the finite invariant actual joint orbit. -/
theorem jointOrbitPolynomialAnnihilation :
    JointOrbitPolynomialAnnihilationStatement K n := by
  intro f hf z b
  have : Module.Finite ℂ (jointOrbitSpan K n f) := hf
  obtain ⟨p, hp, hd, hann⟩ := polynomial_annihilator_of_invariant
    (jointOrbitSpan K n f) (envelopingAction K n (centerInclusion K n z + b.val))
    (center_add_compact_preserves_jointOrbit K n f z b)
  refine ⟨p, hp, hd, ?_⟩
  intro g hg
  rw [← Polynomial.aeval_algHom_apply]
  exact hann g hg

end Langlands.Global.ArchimedeanGL
