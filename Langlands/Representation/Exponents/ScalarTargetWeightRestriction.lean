import Langlands.Representation.Exponents.SelectedWeights
import Mathlib.LinearAlgebra.Dimension.Basic

/-! # Restriction to selected weights for maps into a scalar-character target -/

noncomputable section

namespace Langlands

universe uR uA uM uV uW

variable {R : Type uR} [Field R] {A : Type uA} [Group A]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  (ρ : Representation R M V) (σ : Representation R M W)
  (ι : A →* M) (hι : ∀ a : A, ι a ∈ Subgroup.center M)

/-- An actual scalar action has no generalized weight of a different character.
No smoothness or admissibility of the target is required. -/
theorem generalizedWeightSpace_eq_bot_of_scalar_ne
    (ψ χ : A →* Rˣ)
    (hscalar : ∀ a w, σ (ι a) w = (ψ a : R) • w) (hne : χ ≠ ψ) :
    generalizedWeightSpace σ ι χ hι = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply bot_unique
  intro w hw
  change w = 0
  by_contra hw0
  apply hne
  obtain ⟨K, hK, d, hd⟩ := (mem_generalizedWeightSpace σ ι χ hι w).mp hw
  ext a
  have hs : σ (ι a) = (ψ a : R) • 1 := by
    ext y
    exact hscalar a y
  have hpow := hd a
  have hzero : ((ψ a : R) - (χ a : R)) ^ d • w = 0 := by
    simpa only [hs, ← sub_smul, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply] using hpow
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero
    ((smul_eq_zero.mp hzero).resolve_right hw0))).symm

/-- Every intertwiner into a scalar-character target kills all selected
weights that exclude the scalar character. -/
theorem intertwiner_eq_zero_on_excludedWeights
    (ψ : A →* Rˣ) (hscalar : ∀ a w, σ (ι a) w = (ψ a : R) • w)
    (P : (A →* Rˣ) → Prop) (hψ : P ψ)
    (f : ρ.IntertwiningMap σ) {v : V}
    (hv : v ∈ selectedWeightPart ρ ι hι (fun χ => ¬ P χ)) :
    f v = 0 := by
  have hle : (selectedWeightPart ρ ι hι (fun χ => ¬ P χ)).toSubmodule ≤
      f.toLinearMap.ker := by
    rw [selectedWeightPart_toSubmodule]
    refine iSup_le fun χ => iSup_le fun hχ => ?_
    intro x hx
    have hw := map_mem_generalizedWeightSpace ι χ hι f hx
    rw [generalizedWeightSpace_eq_bot_of_scalar_ne σ ι hι ψ χ hscalar
      (fun he => hχ (he.symm ▸ hψ))] at hw
    exact hw
  exact hle hv

/-- Linear precomposition with the literal selected-weight inclusion. -/
def scalarTargetWeightRestriction (P : (A →* Rˣ) → Prop) :
    (ρ.IntertwiningMap σ) →ₗ[R]
      ((selectedWeightPart ρ ι hι P).toRepresentation.IntertwiningMap σ) where
  toFun f := {
    toLinearMap := f.toLinearMap.comp (selectedWeightPart ρ ι hι P).toSubmodule.subtype
    isIntertwining' m := by
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ f m v.val }
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl

/-- If the selected and excluded parts span and the scalar target character
is selected, restriction detects every intertwiner. -/
theorem scalarTargetWeightRestriction_injective_of_span
    (ψ : A →* Rˣ) (hscalar : ∀ a w, σ (ι a) w = (ψ a : R) • w)
    (P : (A →* Rˣ) → Prop) (hψ : P ψ)
    (hspan : (selectedWeightPart ρ ι hι P).toSubmodule ⊔
      (selectedWeightPart ρ ι hι (fun χ => ¬ P χ)).toSubmodule = ⊤) :
    Function.Injective (scalarTargetWeightRestriction ρ σ ι hι P) := by
  intro f g hfg
  have hker : (selectedWeightPart ρ ι hι P).toSubmodule ⊔
      (selectedWeightPart ρ ι hι (fun χ => ¬ P χ)).toSubmodule ≤ (f - g).toLinearMap.ker := by
    apply sup_le
    · intro x hx
      change f x - g x = 0
      exact sub_eq_zero.mpr (congrArg (fun T => T ⟨x, hx⟩) hfg)
    · intro x hx
      exact intertwiner_eq_zero_on_excludedWeights ρ σ ι hι ψ hscalar P hψ (f - g) hx
  rw [hspan] at hker
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact sub_eq_zero.mp (hker (Submodule.mem_top : x ∈ (⊤ : Submodule R V)))

/-- Admissibility of the source supplies the spanning premise for any
selection containing the scalar target character. -/
theorem scalarTargetWeightRestriction_injective [IsAlgClosed R]
    (hρ : IsAdmissible ρ)
    (ψ : A →* Rˣ) (hscalar : ∀ a w, σ (ι a) w = (ψ a : R) • w)
    (P : (A →* Rˣ) → Prop) (hψ : P ψ) :
    Function.Injective (scalarTargetWeightRestriction ρ σ ι hι P) := by
  apply scalarTargetWeightRestriction_injective_of_span ρ σ ι hι ψ hscalar P hψ
  rw [selectedWeightPart_sup_complement]
  exact generalizedWeightSpace_iSup_eq_top ρ ι hι hρ.1
    (CentralDecomposition.admissible_centerFinite ρ hρ)

/-- The same restriction bounds the cardinal rank of the whole Hom space
by that of the selected-part Hom space, with independent carriers. -/
theorem hom_rank_le_selectedWeightPart_of_scalar [IsAlgClosed R]
    (hρ : IsAdmissible ρ)
    (ψ : A →* Rˣ) (hscalar : ∀ a w, σ (ι a) w = (ψ a : R) • w)
    (P : (A →* Rˣ) → Prop) (hψ : P ψ) :
    Module.rank R (ρ.IntertwiningMap σ) ≤
      Module.rank R ((selectedWeightPart ρ ι hι P).toRepresentation.IntertwiningMap σ) :=
  LinearMap.rank_le_of_injective (scalarTargetWeightRestriction ρ σ ι hι P)
    (scalarTargetWeightRestriction_injective ρ σ ι hι hρ ψ hscalar P hψ)

end Langlands
