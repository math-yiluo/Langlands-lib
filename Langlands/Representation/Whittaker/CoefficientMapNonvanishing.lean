import Langlands.Representation.Whittaker.Transport

/-!
# Nonvanishing of coefficient maps after precomposition

An equivariant functional that restricts nontrivially gives a coefficient map
with nonzero range. The same holds when the coefficient map is restricted to
any invariant subspace that contains its coefficient image.
-/

namespace Langlands.Whittaker

universe uR uG uV uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {N : Subgroup G} {θ : N →* Rˣ}
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Evaluation at the identity shows that a nonzero restricted functional
has a nonzero coefficient image. -/
theorem coefficientMap_comp_range_ne_bot
    (j : ρ.IntertwiningMap σ) (ℓ : functionals N θ σ)
    (hℓ : (functionalsComap j ℓ).val ≠ 0) :
    ((coefficientMap σ ℓ).comp j).range ≠ ⊥ := by
  intro hz
  apply hℓ
  apply LinearMap.ext
  intro x
  have hmem : ((coefficientMap σ ℓ).comp j) x ∈
      ((coefficientMap σ ℓ).comp j).range := ⟨x, rfl⟩
  rw [hz] at hmem
  have hx : ((coefficientMap σ ℓ).comp j) x = 0 := hmem
  have heval := congrArg
    (fun w : (equivariantFunctions N θ).toSubmodule => w.val 1) hx
  change ℓ.val (σ 1 (j x)) = 0 at heval
  change ℓ.val (j x) = 0
  simpa only [map_one, Module.End.one_apply] using heval

/-- Precompose a coefficient map and restrict its codomain to an invariant
subspace containing the entire coefficient image. -/
def coefficientMapCompToSubrepresentation
    (j : ρ.IntertwiningMap σ) (ℓ : functionals N θ σ)
    (M : Subrepresentation (functionRepresentation N θ))
    (hM : coefficientModel σ ℓ ≤ M) :
    ρ.IntertwiningMap M.toRepresentation where
  toLinearMap := ((coefficientMap σ ℓ).toLinearMap.comp j.toLinearMap).codRestrict
    M.toSubmodule (fun x => hM ⟨j x, rfl⟩)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (((coefficientMap σ ℓ).comp j).isIntertwining' g) x

/-- Restricting the codomain to an invariant subspace containing the coefficient
image preserves nonvanishing of the precomposed coefficient map. -/
theorem coefficientMapCompToSubrepresentation_range_ne_bot
    (j : ρ.IntertwiningMap σ) (ℓ : functionals N θ σ)
    (M : Subrepresentation (functionRepresentation N θ))
    (hM : coefficientModel σ ℓ ≤ M)
    (hℓ : (functionalsComap j ℓ).val ≠ 0) :
    (coefficientMapCompToSubrepresentation j ℓ M hM).range ≠ ⊥ := by
  intro hz
  apply coefficientMap_comp_range_ne_bot j ℓ hℓ
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · rintro w ⟨x, rfl⟩
    have hmem : coefficientMapCompToSubrepresentation j ℓ M hM x ∈
        (coefficientMapCompToSubrepresentation j ℓ M hM).range := ⟨x, rfl⟩
    rw [hz] at hmem
    have hx : coefficientMapCompToSubrepresentation j ℓ M hM x = 0 := hmem
    have hx' := congrArg Subtype.val hx
    exact (Submodule.mem_bot R).mpr hx'
  · exact bot_le

end Langlands.Whittaker
