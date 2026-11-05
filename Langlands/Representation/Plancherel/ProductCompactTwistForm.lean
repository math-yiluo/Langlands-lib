import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Representation.Plancherel.CoefficientTensorForm
import Langlands.Representation.Unitary.Twist

/-!
# Hermitian compatibility of the actual compact twist comparison

The smooth-dual twist equivalence preserves every underlying functional.
Unitary twisting therefore preserves the Hermitian dual identification and the
whole coefficient-tensor form, before any compact induction or integration.
-/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands

universe uG uI uV

namespace InvariantPositiveForm

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hρ : IsAdmissible ρ)
  (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
  (hu : ∀ g, ‖(χ g : ℂ)‖ = 1)

/-- Removing a smooth unitary twist from an actual smooth functional
commutes with the conjugate-linear Hermitian identification. -/
theorem smoothDualEquiv_twist (b : InvariantPositiveForm ρ) (v : V) :
    smoothContragredientTwistEquiv χ ρ hχ
        ((b.twist χ hu).smoothDualEquiv hcof
          ((isAdmissible_twist_iff χ ρ hχ).mpr hρ) v) =
      b.smoothDualEquiv hcof hρ v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  rfl

/-- The inverse Hermitian identifications retain the same vector when
the smooth functional is transported by the actual twist equivalence. -/
theorem smoothDualEquiv_twist_symm (b : InvariantPositiveForm ρ)
    (ℓ : SmoothDual (Langlands.twist χ ρ)) :
    (b.smoothDualEquiv hcof hρ).symm
        (smoothContragredientTwistEquiv χ ρ hχ ℓ) =
      ((b.twist χ hu).smoothDualEquiv hcof
        ((isAdmissible_twist_iff χ ρ hχ).mpr hρ)).symm ℓ := by
  apply (b.smoothDualEquiv hcof hρ).injective
  rw [LinearEquiv.apply_symm_apply, ← smoothDualEquiv_twist hcof hρ χ hχ hu b,
    LinearEquiv.apply_symm_apply]

end InvariantPositiveForm

namespace HarishChandraSchwartz

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hρ : IsAdmissible ρ)
  (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
  (hu : ∀ g, ‖(χ g : ℂ)‖ = 1)

/-- The positive form on the actual smooth dual is preserved on all
functionals by removal of a smooth unitary twist. -/
theorem dualInvariantForm_twist_inner (b : InvariantPositiveForm ρ)
    (ℓ m : SmoothDual (Langlands.twist χ ρ)) :
    (dualInvariantForm b hcof hρ).inner
        (smoothContragredientTwistEquiv χ ρ hχ ℓ)
        (smoothContragredientTwistEquiv χ ρ hχ m) =
      (dualInvariantForm (b.twist χ hu) hcof
        ((isAdmissible_twist_iff χ ρ hχ).mpr hρ)).inner ℓ m := by
  change b.inner
      ((b.smoothDualEquiv hcof hρ).symm (smoothContragredientTwistEquiv χ ρ hχ m))
      ((b.smoothDualEquiv hcof hρ).symm (smoothContragredientTwistEquiv χ ρ hχ ℓ)) =
    b.inner
      (((b.twist χ hu).smoothDualEquiv hcof
        ((isAdmissible_twist_iff χ ρ hχ).mpr hρ)).symm m)
      (((b.twist χ hu).smoothDualEquiv hcof
        ((isAdmissible_twist_iff χ ρ hχ).mpr hρ)).symm ℓ)
  rw [b.smoothDualEquiv_twist_symm hcof hρ χ hχ hu m,
    b.smoothDualEquiv_twist_symm hcof hρ χ hχ hu ℓ]

end HarishChandraSchwartz

namespace Plancherel

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (χ : unramifiedCharacters ν) (hu : ∀ m, ‖(χ.val m : ℂ)‖ = 1)
  (A : SmoothRep.{0, uG, uV} ℂ M)
  (hcof : ∀ K : OpenSubgroup M, ∃ L : OpenSubgroup M,
    IsCompact (L : Set M) ∧ L ≤ K)
  (hA : IsAdmissible A.representation)
  (b : InvariantPositiveForm A.representation)

/-- The existing compact twist tensor map preserves the entire actual
coefficient-tensor form for a unitary unramified character. -/
theorem productCompactTwistTensorEquiv_inner
    (t s : CoefficientTensor
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    (coefficientTensorInvariantForm A hcof hA b).inner
        (productCompactTwistTensorEquiv ν χ A t)
        (productCompactTwistTensorEquiv ν χ A s) =
      (coefficientTensorInvariantForm
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hcof
        ((isAdmissible_twist_iff χ.val.toMonoidHom A.representation
          (unramifiedCharacter_isOpen_ker ν χ)).mpr hA)
        (b.twist χ.val.toMonoidHom hu)).inner t s := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    induction s using TensorProduct.inductionOn with
    | tmul w m =>
      change (coefficientTensorInvariantForm A hcof hA b).inner
        (v ⊗ₜ[ℂ] smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
          (unramifiedCharacter_isOpen_ker ν χ) ℓ)
        (w ⊗ₜ[ℂ] smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
          (unramifiedCharacter_isOpen_ker ν χ) m) = _
      exact (coefficientTensorInvariantForm_inner_tmul A hcof hA b v w _ _).trans
        ((congrArg (fun z : ℂ => b.inner v w * z)
          (HarishChandraSchwartz.dualInvariantForm_twist_inner
            hcof hA χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)
            hu b ℓ m)).trans
          (coefficientTensorInvariantForm_inner_tmul
            (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hcof
            ((isAdmissible_twist_iff χ.val.toMonoidHom A.representation
              (unramifiedCharacter_isOpen_ker ν χ)).mpr hA)
            (b.twist χ.val.toMonoidHom hu) v w ℓ m).symm)
    | add s s' hs hs' =>
      simp only [map_add, InvariantPositiveForm.add_right, hs, hs']
  | add t t' ht ht' =>
    simp only [map_add, PreInnerProductSpace.Core.add_left, ht, ht']

/-- Equip the already constructed compact twist equivalence with its
proved full Hermitian compatibility, without adding a carrier topology. -/
def productCompactTwistTensorIsometry :
    {E : CoefficientTensor
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) ≃ₗ[ℂ]
        CoefficientTensor A //
      ∀ t s, (coefficientTensorInvariantForm A hcof hA b).inner (E t) (E s) =
        (coefficientTensorInvariantForm
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hcof
          ((isAdmissible_twist_iff χ.val.toMonoidHom A.representation
            (unramifiedCharacter_isOpen_ker ν χ)).mpr hA)
          (b.twist χ.val.toMonoidHom hu)).inner t s} :=
  ⟨productCompactTwistTensorEquiv ν χ A,
    productCompactTwistTensorEquiv_inner ν χ hu A hcof hA b⟩

@[simp]
theorem productCompactTwistTensorIsometry_val :
    (productCompactTwistTensorIsometry ν χ hu A hcof hA b).val =
      productCompactTwistTensorEquiv ν χ A := rfl

end Plancherel

end Langlands
