import Langlands.Representation.Plancherel.CoefficientTensorForm

/-!
# Hermitian transport of coefficient tensors

The canonical coefficient transport uses an equivalence on vectors and inverse
pullback on smooth functionals. Naturality of the actual Hermitian dual
identification proves that this transport preserves the full tensor form.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands

universe uR uG uV uW

namespace InvariantPositiveForm

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ)

/-- The actual conjugate-linear Hermitian identification commutes with an
equivalence on vectors and inverse pullback on smooth functionals. -/
theorem smoothDualEquiv_ofEquiv (b : InvariantPositiveForm σ)
    (e : ρ.Equiv σ) (v : V) :
    smoothContragredientEquiv e.symm
        ((b.ofEquiv e).smoothDualEquiv hcof hρ v) =
      b.smoothDualEquiv hcof hσ (e v) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  change b.inner (e v) (e (e.symm w)) = b.inner (e v) w
  rw [e.apply_symm_apply]

/-- The inverse Hermitian identifications satisfy the corresponding
naturality identity on every smooth functional. -/
theorem smoothDualEquiv_ofEquiv_symm (b : InvariantPositiveForm σ)
    (e : ρ.Equiv σ) (ℓ : SmoothDual ρ) :
    (b.smoothDualEquiv hcof hσ).symm
        (smoothContragredientEquiv e.symm ℓ) =
      e (((b.ofEquiv e).smoothDualEquiv hcof hρ).symm ℓ) := by
  apply (b.smoothDualEquiv hcof hσ).injective
  rw [LinearEquiv.apply_symm_apply,
    ← smoothDualEquiv_ofEquiv hcof hρ hσ b e,
    LinearEquiv.apply_symm_apply]

end InvariantPositiveForm

namespace HarishChandraSchwartz

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ)

/-- Pullback of a positive form along an equivalence commutes with the
actual positive form on the smooth dual. No irreducibility is required. -/
theorem dualInvariantForm_ofEquiv (b : InvariantPositiveForm σ)
    (e : ρ.Equiv σ) :
    dualInvariantForm (b.ofEquiv e) hcof hρ =
      (dualInvariantForm b hcof hσ).ofEquiv
        (smoothContragredientEquiv e.symm) := by
  apply InvariantPositiveForm.ext_inner
  intro ℓ m
  change b.inner
      (e (((b.ofEquiv e).smoothDualEquiv hcof hρ).symm m))
      (e (((b.ofEquiv e).smoothDualEquiv hcof hρ).symm ℓ)) =
    b.inner
      ((b.smoothDualEquiv hcof hσ).symm (smoothContragredientEquiv e.symm m))
      ((b.smoothDualEquiv hcof hσ).symm (smoothContragredientEquiv e.symm ℓ))
  rw [b.smoothDualEquiv_ofEquiv_symm hcof hρ hσ e m,
    b.smoothDualEquiv_ofEquiv_symm hcof hρ hσ e ℓ]

end HarishChandraSchwartz

namespace Plancherel

section CoefficientEquivalence

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {A : SmoothRep.{uR, uG, uV} R G} {B : SmoothRep.{uR, uG, uW} R G}

/-- The existing coefficient-tensor linear transport, equipped with its
proved intertwining of the actual product-group actions. -/
def coefficientTensorCongrEquiv (e : A.representation.Equiv B.representation) :
    (coefficientTensorAction A).Equiv (coefficientTensorAction B) where
  __ := coefficientTensorCongr e
  isIntertwining' x := by
    apply LinearMap.ext
    intro t
    exact coefficientTensorCongr_action e x t

@[simp]
theorem coefficientTensorCongrEquiv_apply
    (e : A.representation.Equiv B.representation) (t : CoefficientTensor A) :
    coefficientTensorCongrEquiv e t = coefficientTensorCongr e t := rfl

end CoefficientEquivalence

section HermitianForm

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
    IsCompact (L : Set G) ∧ L ≤ K)
  (hA : IsAdmissible A.representation) (hB : IsAdmissible B.representation)

/-- The full coefficient-tensor form commutes with canonical representative
transport, for any supplied positive form on the target representation. -/
theorem coefficientTensorInvariantForm_ofEquiv
    (b : InvariantPositiveForm B.representation)
    (e : A.representation.Equiv B.representation) :
    (coefficientTensorInvariantForm B hcof hB b).ofEquiv
        (coefficientTensorCongrEquiv e) =
      coefficientTensorInvariantForm A hcof hA (b.ofEquiv e) := by
  have hd (ℓ m : SmoothDual A.representation) :
      (HarishChandraSchwartz.dualInvariantForm b hcof hB).inner
          (smoothContragredientEquiv e.symm ℓ)
          (smoothContragredientEquiv e.symm m) =
        (HarishChandraSchwartz.dualInvariantForm (b.ofEquiv e) hcof hA).inner ℓ m := by
    exact (congrArg (fun c => c.inner ℓ m)
      (HarishChandraSchwartz.dualInvariantForm_ofEquiv hcof hA hB b e)).symm
  apply InvariantPositiveForm.ext_inner
  intro t s
  change (coefficientTensorInvariantForm B hcof hB b).inner
    (coefficientTensorCongr e t) (coefficientTensorCongr e s) =
      (coefficientTensorInvariantForm A hcof hA (b.ofEquiv e)).inner t s
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    induction s using TensorProduct.inductionOn with
    | tmul w m =>
      change (coefficientTensorInvariantForm B hcof hB b).inner
        (e v ⊗ₜ[ℂ] smoothContragredientEquiv e.symm ℓ)
        (e w ⊗ₜ[ℂ] smoothContragredientEquiv e.symm m) = _
      rw [coefficientTensorInvariantForm_inner_tmul,
        coefficientTensorInvariantForm_inner_tmul, hd]
      rfl
    | add s s' hs hs' =>
      simp only [map_add, InvariantPositiveForm.add_right, hs, hs']
  | add t t' ht ht' =>
    simp only [map_add, PreInnerProductSpace.Core.add_left, ht, ht']

end HermitianForm

end Plancherel

end Langlands
