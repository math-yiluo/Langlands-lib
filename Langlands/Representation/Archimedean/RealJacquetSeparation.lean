import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.KFiniteDual
import Langlands.Global.ArchimedeanCompact

/-!
# Separating a vector from a subrepresentation by the dual principal series

Let `ds, ds'` be lists of real blocks whose `O(n)`-finite principal series functions are paired
by `RealPrincipalSeriesDuality.pairing n ds ds'` (integration over `O(n)`), and assume that
this pairing separates the points of the first factor. If `N` is an `O(n)`-stable subspace of
the `O(n)`-finite functions of `ds` and `w ∉ N`, then some `O(n)`-finite function `ψ` of `ds'`
is orthogonal to `N` and pairs nontrivially with `w` (`exists_orthogonal_pairing_ne_zero`).

The proof uses the block decomposition of the admissible `O(n)`-module (Library
`Langlands.Representation.KFiniteDual`): a block component of `w` lies outside `N`; a functional
on that finite-dimensional block separates it from `N`; the resulting `O(n)`-finite functional
is represented by the pairing, because the represented functionals form a separating
subrepresentation of the finite dual (`KFiniteDual.mem_of_separating`).
-/

noncomputable section

open MeasureTheory

open scoped Manifold ContDiff Matrix.Norms.Operator MonoidAlgebra

namespace Langlands.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace RealJacquetSeparation

open RealPrincipalSeriesDuality Langlands.LocalFactor.Archimedean Langlands.KFiniteDual

attribute [local instance] measurableSpaceK

local instance borelSpaceK₄ (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-- The `O(n)`-finite functions of the real standard module of `ds`. -/
abbrev KF (n : ℕ) (ds : List RealBlock) : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

variable {ds ds' : List RealBlock}

/-- The pairing is invariant under simultaneous right translation by `O(n)`. -/
theorem pairing_rep_inv (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n ds) (ψ : KF n ds') :
    pairing n ds ds' (realStandardRep n ds k⁻¹ f) ψ =
      pairing n ds ds' f (realStandardRep n ds' k ψ) := by
  rw [pairing_apply, pairing_apply]
  let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits k, k.2⟩
  rw [← integral_mul_right_eq_self _ k']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [realStandardRep_apply_coe]
  change (f : Langlands.GeneralLinear n ℝ → ℂ)
      ((x : Langlands.GeneralLinear n ℝ) * Unitary.toUnits k * Unitary.toUnits k⁻¹) *
      (ψ : Langlands.GeneralLinear n ℝ → ℂ) ((x : Langlands.GeneralLinear n ℝ) * Unitary.toUnits k) =
    (f : Langlands.GeneralLinear n ℝ → ℂ) (x : Langlands.GeneralLinear n ℝ) *
      (ψ : Langlands.GeneralLinear n ℝ → ℂ) ((x : Langlands.GeneralLinear n ℝ) * Unitary.toUnits k)
  rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

variable (ds ds') in
/-- The functionals `f ↦ pairing f ψ` on the `O(n)`-finite functions of `ds`. -/
def dualOf : KF n ds' →ₗ[ℂ] Module.Dual ℂ (KF n ds) := (pairing n ds ds').flip

theorem dualOf_apply (ψ : KF n ds') (f : KF n ds) : dualOf ds ds' ψ f = pairing n ds ds' f ψ :=
  rfl

theorem dual_dualOf (k : Matrix.unitaryGroup (Fin n) ℝ) (ψ : KF n ds') :
    (realStandardRep n ds).dual k (dualOf ds ds' ψ) = dualOf ds ds' (realStandardRep n ds' k ψ) :=
  LinearMap.ext fun f => by
    rw [dual_apply_apply, dualOf_apply, dualOf_apply]
    exact pairing_rep_inv k f ψ

theorem isFiniteVector_dualOf (ψ : KF n ds') :
    FiniteVectors.IsFiniteVector (realStandardRep n ds).dual (dualOf ds ds' ψ) := by
  have hψ : Module.Finite ℂ (FiniteVectors.orbitSpan (realStandardRep n ds') ψ) :=
    (isRealGKModule_realStandardModule n ds').1 ψ
  have hle : FiniteVectors.orbitSpan (realStandardRep n ds).dual (dualOf ds ds' ψ) ≤
      (FiniteVectors.orbitSpan (realStandardRep n ds') ψ).map (dualOf ds ds') := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨_, FiniteVectors.action_mem_orbitSpan _ k ψ, (dual_dualOf k ψ).symm⟩
  exact Submodule.finiteDimensional_of_le hle

variable (ds ds') in
/-- The represented functionals, as a subrepresentation of the dual. -/
def representedSub : Subrepresentation (realStandardRep n ds).dual where
  toSubmodule := LinearMap.range (dualOf ds ds')
  apply_mem_toSubmodule k := by
    rintro _ ⟨ψ, rfl⟩
    exact ⟨_, (dual_dualOf k ψ).symm⟩

/-- **Separation.** If the pairing separates the points of the `O(n)`-finite functions of `ds`,
then every `w` outside an `O(n)`-stable subspace `N` is separated from `N` by some `ψ`. -/
theorem exists_orthogonal_pairing_ne_zero
    (hsep : ∀ f : KF n ds, f ≠ 0 → ∃ ψ : KF n ds', pairing n ds ds' f ψ ≠ 0)
    (N : Subrepresentation (realStandardRep n ds)) {w : KF n ds} (hw : w ∉ N) :
    ∃ ψ : KF n ds', (∀ f ∈ N, pairing n ds ds' f ψ = 0) ∧ pairing n ds ds' w ψ ≠ 0 := by
  have hgk := isRealGKModule_realStandardModule n ds
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℝ]
      (realStandardRep n ds).asModule := isSemisimpleModule hgk.1 hgk.2.1
  have hblock := finiteDimensional_block hgk.1 hgk.2.1 (realStandardAdmissible n ds)
  obtain ⟨t, -, ht⟩ := exists_finset_proj (ρ := realStandardRep n ds) w
  obtain ⟨c, -, hc⟩ : ∃ c ∈ t, proj c w ∉ N := by
    by_contra h
    push Not at h
    exact hw (ht ▸ Submodule.sum_mem N.toSubmodule h)
  have := hblock c
  let Nc : Submodule ℂ (blockSub c).toSubmodule :=
    N.toSubmodule.comap (blockSub c).toSubmodule.subtype
  have hnot : projTo c w ∉ Nc := hc
  obtain ⟨φ, hφ, hφN⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Nc) (x := projTo c w) hnot inferInstance
  have hℓ := isFiniteVector_comp_projTo c φ
  have hW' : ∀ x ∈ representedSub ds ds', FiniteVectors.IsFiniteVector
      (realStandardRep n ds).dual x := by
    rintro _ ⟨ψ, rfl⟩
    exact isFiniteVector_dualOf ψ
  have hsep' : ∀ f : KF n ds, (∀ x ∈ representedSub ds ds', x f = 0) → f = 0 := by
    intro f hf
    by_contra hf0
    obtain ⟨ψ, hψ⟩ := hsep f hf0
    exact hψ (hf _ ⟨ψ, rfl⟩)
  obtain ⟨ψ, hψ⟩ := mem_of_separating hblock (representedSub ds ds') hW' hsep' hℓ
  refine ⟨ψ, fun f hf => ?_, ?_⟩
  · rw [← dualOf_apply, hψ]
    have hfc : projTo c f ∈ Nc := proj_mem_of_mem c N hf
    have : φ (projTo c f) ∈ Nc.map φ := Submodule.mem_map_of_mem hfc
    rw [hφN] at this
    exact (Submodule.mem_bot ℂ).mp this
  · rw [← dualOf_apply, hψ]
    exact hφ

end RealJacquetSeparation

end Langlands.Archimedean
