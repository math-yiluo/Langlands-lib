import Langlands.Representation.Exponents.Central
import Mathlib.Analysis.Complex.Basic

/-!
# The unitary central part of a complex representation

This is the algebraic sum of generalized full-center character spaces with
unitary character. No temperedness or finite-length assertion is made here.
-/

noncomputable section

namespace Langlands

universe uG uV uW uX

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- The sum of all generalized central-character spaces whose character has
absolute value one on every central element. -/
def unitaryCentralPart (ρ : Representation ℂ G V) : Subrepresentation ρ where
  toSubmodule := ⨆ χ : {χ : Subgroup.center G →* ℂˣ // ∀ z, ‖(χ z : ℂ)‖ = 1},
    (generalizedCentralCharacterSpace ρ χ.val).toSubmodule
  apply_mem_toSubmodule g := by
    have hle : (⨆ χ : {χ : Subgroup.center G →* ℂˣ // ∀ z, ‖(χ z : ℂ)‖ = 1},
        (generalizedCentralCharacterSpace ρ χ.val).toSubmodule) ≤
        Submodule.comap (ρ g) (⨆ χ : {χ : Subgroup.center G →* ℂˣ //
          ∀ z, ‖(χ z : ℂ)‖ = 1},
          (generalizedCentralCharacterSpace ρ χ.val).toSubmodule) := by
      refine iSup_le fun χ => ?_
      intro v hv
      exact (le_iSup (fun ψ : {ψ : Subgroup.center G →* ℂˣ //
        ∀ z, ‖(ψ z : ℂ)‖ = 1} =>
        (generalizedCentralCharacterSpace ρ ψ.val).toSubmodule) χ)
        ((generalizedCentralCharacterSpace ρ χ.val).apply_mem_toSubmodule g hv)
    intro v hv
    exact hle hv

/-- Every unitary generalized character space lies in the constructed part. -/
theorem generalizedCentralCharacterSpace_le_unitaryCentralPart
    (ρ : Representation ℂ G V) (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) :
    generalizedCentralCharacterSpace ρ χ ≤ unitaryCentralPart ρ :=
  le_iSup (fun ψ : {ψ : Subgroup.center G →* ℂˣ // ∀ z, ‖(ψ z : ℂ)‖ = 1} =>
    (generalizedCentralCharacterSpace ρ ψ.val).toSubmodule) ⟨χ, hχ⟩

/-- The part is the least invariant subspace containing those character spaces. -/
theorem unitaryCentralPart_le_iff (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) :
    unitaryCentralPart ρ ≤ S ↔ ∀ (χ : Subgroup.center G →* ℂˣ),
      (∀ z, ‖(χ z : ℂ)‖ = 1) → generalizedCentralCharacterSpace ρ χ ≤ S := by
  change (⨆ χ : {χ : Subgroup.center G →* ℂˣ // ∀ z, ‖(χ z : ℂ)‖ = 1},
    (generalizedCentralCharacterSpace ρ χ.val).toSubmodule) ≤ S.toSubmodule ↔ _
  rw [iSup_le_iff]
  exact ⟨fun h χ hχ => h ⟨χ, hχ⟩, fun h χ => h χ.val χ.property⟩

/-- A unitary scalar central action places the whole representation in the part. -/
theorem unitaryCentralPart_eq_top_of_scalar_action (ρ : Representation ℂ G V)
    (χ : Subgroup.center G →* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hacts : ∀ (z : Subgroup.center G) (v : V), ρ (z : G) v = (χ z : ℂ) • v) :
    unitaryCentralPart ρ = ⊤ := by
  apply le_antisymm le_top
  intro v _
  apply generalizedCentralCharacterSpace_le_unitaryCentralPart ρ χ hχ
  apply (mem_generalizedCentralCharacterSpace ρ χ v).mpr
  refine ⟨1, fun z => ?_⟩
  simp [hacts z v]

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  {τ : Representation ℂ G X}

/-- Every intertwiner preserves the unitary central part. -/
theorem map_mem_unitaryCentralPart (f : ρ.IntertwiningMap σ) {v : V}
    (hv : v ∈ unitaryCentralPart ρ) : f v ∈ unitaryCentralPart σ := by
  have hle : (unitaryCentralPart ρ).toSubmodule ≤
      Submodule.comap f.toLinearMap (unitaryCentralPart σ).toSubmodule := by
    refine iSup_le fun χ => ?_
    intro x hx
    exact generalizedCentralCharacterSpace_le_unitaryCentralPart σ χ.val χ.property
      (map_mem_generalizedCentralCharacterSpace f χ.val hx)
  exact hle hv

/-- Restriction of an ambient intertwiner to the actual unitary central parts. -/
def unitaryCentralPartMap (f : ρ.IntertwiningMap σ) :
    (unitaryCentralPart ρ).toRepresentation.IntertwiningMap
      (unitaryCentralPart σ).toRepresentation where
  toFun v := ⟨f v, map_mem_unitaryCentralPart f v.property⟩
  map_add' v w := Subtype.ext (map_add f (v : V) (w : V))
  map_smul' c v := Subtype.ext (map_smul f c (v : V))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining ρ σ f g (v : V)

@[simp] theorem unitaryCentralPartMap_apply (f : ρ.IntertwiningMap σ)
    (v : unitaryCentralPart ρ) :
    (unitaryCentralPartMap f v : W) = f (v : V) := rfl

@[simp] theorem unitaryCentralPartMap_id (ρ : Representation ℂ G V) :
    unitaryCentralPartMap (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (unitaryCentralPart ρ).toRepresentation := by
  ext v
  rfl

@[simp] theorem unitaryCentralPartMap_comp (g : σ.IntertwiningMap τ)
    (f : ρ.IntertwiningMap σ) :
    unitaryCentralPartMap (g.comp f) =
      (unitaryCentralPartMap g).comp (unitaryCentralPartMap f) := by
  ext v
  rfl

/-- The inclusion into the ambient representation is an actual intertwiner. -/
def unitaryCentralPartInclusion (ρ : Representation ℂ G V) :
    (unitaryCentralPart ρ).toRepresentation.IntertwiningMap ρ where
  toLinearMap := (unitaryCentralPart ρ).toSubmodule.subtype
  isIntertwining' _ := rfl

theorem unitaryCentralPartInclusion_injective (ρ : Representation ℂ G V) :
    Function.Injective (unitaryCentralPartInclusion ρ) := Subtype.val_injective

/-- Restriction commutes with the actual inclusions. -/
theorem unitaryCentralPartInclusion_natural (f : ρ.IntertwiningMap σ) :
    (unitaryCentralPartInclusion σ).comp (unitaryCentralPartMap f) =
      f.comp (unitaryCentralPartInclusion ρ) := by
  ext v
  rfl

/-- Restrict an equivariant linear equivalence and its inverse. -/
def unitaryCentralPartEquiv (e : ρ.Equiv σ) :
    (unitaryCentralPart ρ).toRepresentation.Equiv
      (unitaryCentralPart σ).toRepresentation where
  __ := unitaryCentralPartMap e.toIntertwiningMap
  invFun := unitaryCentralPartMap e.symm.toIntertwiningMap
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv v := Subtype.ext (e.apply_symm_apply v)

end Langlands
