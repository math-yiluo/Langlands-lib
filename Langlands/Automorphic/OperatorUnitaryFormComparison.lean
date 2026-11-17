import Langlands.Automorphic.CuspidalConjugateRealization
import Langlands.Automorphic.UnitaryContragredientCriterion
import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-! # Comparison of positive forms on actual irreducible operator realizations -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance comparisonRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance comparisonStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n}

/-- The actual pointwise-conjugate realization paired by the supplied positive form. -/
def conjugatePairing (b : S.UnitaryForm) :
    S.Space →ₗ[ℂ] S.conjugate.Space →ₗ[ℂ] ℂ :=
  b.finiteForm.conjPairing S.conjugateEquiv

@[simp]
theorem conjugatePairing_apply (b : S.UnitaryForm) (f : S.Space) (g : S.conjugate.Space) :
    b.conjugatePairing f g = b.inner (S.conjugateEquiv.symm g) f := rfl

/-- Joint admissibility makes this specified pairing perfect on the actual joint dual. -/
theorem conjugatePairing_isContragredient (b : S.UnitaryForm) (hA : S.IsJointlyAdmissible) :
    S.IsContragredientPairing S.conjugate b.conjugatePairing := by
  let b₀ := b.finiteForm
  let Mfin := b₀.conjPairingIntertwining S.conjugateEquiv b₀.invariant S.conjugateEquiv_finite
  let Mcpt := b₀.conjPairingIntertwining S.conjugateEquiv b.compact_invariant
    S.conjugateEquiv_compact
  refine ⟨⟨b₀.conjPairing_invariant S.conjugateEquiv b₀.invariant S.conjugateEquiv_finite,
    b₀.conjPairing_invariant S.conjugateEquiv b.compact_invariant S.conjugateEquiv_compact,
    fun X => b₀.conjPairing_skew S.conjugateEquiv (b.real_skew X)
      (S.conjugateEquiv_lieAction X)⟩,
    fun x => ⟨Langlands.isSmoothVector_map Mfin (S.conjugate.finiteRepresentation_isSmooth x),
      (S.conjugate.compactRepresentation_isFiniteVector x).map Mcpt⟩,
    b₀.conjPairing_flip_injective S.conjugateEquiv, fun l hl => ?_⟩
  obtain ⟨g, hg⟩ := b₀.exists_inner_eq_of_contragredient b.compact_invariant
    S.finiteRepresentation_compactRepresentation S.finiteRepresentation_isSmooth
    S.compactRepresentation_isFiniteVector exists_compact_openSubgroup_le hA hl.1 hl.2
  exact ⟨S.conjugateEquiv g, LinearMap.ext fun y => by
    change b₀.inner (S.conjugateEquiv.symm (S.conjugateEquiv g)) y = l y
    rw [S.conjugateEquiv.symm_apply_apply]
    exact hg y⟩

set_option maxHeartbeats 2000000 in
/-- The comparison of two specified pairings retains their compatibility equation. -/
theorem exists_conjugate_equivalence (b c : S.UnitaryForm) (hA : S.IsJointlyAdmissible) :
    ∃ e : S.conjugate.Equivalence S.conjugate,
      ∀ x, b.conjugatePairing.flip (e x) = c.conjugatePairing.flip x := by
  classical
  obtain ⟨hB, hBc, hinj, hsurj⟩ := b.conjugatePairing_isContragredient hA
  obtain ⟨hC, hCc, hinjC, hsurjC⟩ := c.conjugatePairing_isContragredient hA
  have hrange : LinearMap.range c.conjugatePairing.flip =
      LinearMap.range b.conjugatePairing.flip := by
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      exact hsurj _ (hCc x)
    · rintro ⟨x, rfl⟩
      exact hsurjC _ (hBc x)
  let e : S.conjugate.Space ≃ₗ[ℂ] S.conjugate.Space :=
    (LinearEquiv.ofInjective c.conjugatePairing.flip hinjC).trans
      ((LinearEquiv.ofEq _ _ hrange).trans
        (LinearEquiv.ofInjective b.conjugatePairing.flip hinj).symm)
  have he : ∀ x, b.conjugatePairing.flip (e x) = c.conjugatePairing.flip x := fun x =>
    LinearEquiv.ofInjective_symm_apply (f := b.conjugatePairing.flip) (h := hinj)
      (LinearEquiv.ofEq _ _ hrange (LinearEquiv.ofInjective c.conjugatePairing.flip hinjC x))
  exact ⟨Equivalence.ofGenerators e
    (hC.comparison_finite hB hinj e.toLinearMap he)
    (hC.comparison_compact hB hinj e.toLinearMap he)
    (envelopingAction_comm_of_lieAction e
      (hC.comparison_lieAction hB hinj e.toLinearMap he)), he⟩

/-- Two full invariant positive forms on an irreducible jointly admissible actual
realization are positive real scalar multiples. -/
theorem exists_pos_scalar (b c : S.UnitaryForm) (hS : S.IsIrreducible)
    (hA : S.IsJointlyAdmissible) :
    ∃ a : ℝ, 0 < a ∧ ∀ f g : S.Space, c.inner f g = (a : ℂ) * b.inner f g := by
  obtain ⟨e, he⟩ := exists_conjugate_equivalence b c hA
  obtain ⟨z, hz⟩ := S.conjugate.exists_eq_smul_of_commute
    (S.conjugate_isIrreducible_iff.mpr hS) e.toLinearEquiv.toLinearMap
    (fun a f => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap a f)
  have hscalar (f g : S.Space) : c.inner f g = z * b.inner f g := by
    calc
      c.inner f g = c.conjugatePairing g (S.conjugateEquiv f) := by
        rw [conjugatePairing_apply, S.conjugateEquiv.symm_apply_apply]
      _ = b.conjugatePairing g (e (S.conjugateEquiv f)) :=
        (LinearMap.congr_fun (he (S.conjugateEquiv f)) g).symm
      _ = b.conjugatePairing g (z • S.conjugateEquiv f) :=
        congrArg (b.conjugatePairing g) (hz _)
      _ = z * b.inner f g := by
        rw [map_smul, conjugatePairing_apply, S.conjugateEquiv.symm_apply_apply]
        rfl
  have hnt : Nontrivial (Subrepresentation S.representation) := hS.toNontrivial
  obtain ⟨f, hf⟩ : ∃ f : S.Space, f ≠ 0 := by
    by_contra! h
    apply (bot_ne_top : (⊥ : Subrepresentation S.representation) ≠ ⊤)
    apply Subrepresentation.ext
    change (⊥ : Submodule ℂ S.Space) = ⊤
    rw [eq_comm, eq_bot_iff]
    intro x _
    exact (Submodule.mem_bot ℂ).mpr (h x)
  have hbpos : 0 < (b.inner f f).re := by
    change 0 < (Inner.inner ℂ (b.finiteForm.toNormedCarrier f)
      (b.finiteForm.toNormedCarrier f)).re
    exact (re_inner_self_pos (𝕜 := ℂ)).mpr
      (b.finiteForm.toNormedCarrier.map_ne_zero_iff.mpr hf)
  have hcpos : 0 < (c.inner f f).re := by
    change 0 < (Inner.inner ℂ (c.finiteForm.toNormedCarrier f)
      (c.finiteForm.toNormedCarrier f)).re
    exact (re_inner_self_pos (𝕜 := ℂ)).mpr
      (c.finiteForm.toNormedCarrier.map_ne_zero_iff.mpr hf)
  have hbim : (b.inner f f).im = 0 :=
    inner_self_im (𝕜 := ℂ) (b.finiteForm.toNormedCarrier f)
  have hcim : (c.inner f f).im = 0 :=
    inner_self_im (𝕜 := ℂ) (c.finiteForm.toNormedCarrier f)
  have hzim : z.im = 0 := by
    have h := congrArg Complex.im (hscalar f f)
    rw [Complex.mul_im, hbim, hcim, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (ne_of_gt hbpos)
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzim]
  refine ⟨z.re, ?_, fun f g => (hscalar f g).trans (congrArg (· * b.inner f g) hzreal.symm)⟩
  have h := congrArg Complex.re (hscalar f f)
  rw [Complex.mul_re, hbim, mul_zero, sub_zero] at h
  rw [h] at hcpos
  exact (mul_pos_iff_of_pos_right hbpos).mp hcpos

end OperatorRealization.UnitaryForm

/-- Internal form comparison for actual irreducible jointly admissible realizations,
with arbitrary number-field universe and rank. -/
def OperatorUnitaryFormComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S : OperatorRealization F n),
    S.IsIrreducible → S.IsJointlyAdmissible → ∀ b c : S.UnitaryForm,
      ∃ a : ℝ, 0 < a ∧ ∀ f g : S.Space, c.inner f g = (a : ℂ) * b.inner f g

/-- Positive form comparison, retaining precisely the stated actual hypotheses. -/
theorem operatorUnitaryFormComparison : OperatorUnitaryFormComparisonStatement.{u} := by
  intro F _ _ n S hS hA b c
  exact b.exists_pos_scalar c hS hA

end Langlands.Automorphic
