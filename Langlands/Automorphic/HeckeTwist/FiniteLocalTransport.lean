import Langlands.Automorphic.FiniteLocalDeterminantTransport
import Langlands.Automorphic.HeckeTwist.FiniteLocalTwist
import Langlands.Automorphic.CentralCharacterDeterminantMultiplier
import Mathlib.RepresentationTheory.Irreducible

/-! # Transport along finite and local twists by any Hecke determinant character

Multiplication by `χ ∘ det`, for an arbitrary Hecke character `χ`, transports invariant
subspaces, irreducibility, central characters and cuspidality between a finite or local
realization and its twist. This is the finite-order-free version of
`Langlands.Automorphic.FiniteLocalDeterminantTransport`.
-/

noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance heckeFiniteLocalTransportRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeFiniteLocalTransportContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeFiniteLocalTransportSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeFiniteLocalTransportFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

private def scalarCovariantSubrepresentationOrderIso
    {G V W : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (η : G →* ℂˣ) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ g f, τ g (e f) = (η g : ℂ) • e (ρ g f)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun P :=
    { toSubmodule := P.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule g _ hf := by
        change ∃ f, f ∈ P.toSubmodule ∧ e f = _ at hf
        obtain ⟨f, hf, rfl⟩ := hf
        rw [hc]
        exact Submodule.smul_mem _ _
          (Submodule.mem_map_of_mem (P.apply_mem_toSubmodule g hf)) }
  invFun Q :=
    { toSubmodule := Q.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule g f hf := by
        change e (ρ g f) ∈ Q
        have hm := Q.toSubmodule.smul_mem ((η g)⁻¹ : ℂˣ).val
          (Q.apply_mem_toSubmodule g hf)
        change ((η g)⁻¹ : ℂˣ).val • τ g (e f) ∈ Q.toSubmodule at hm
        rw [hc, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at hm
        exact hm }
  left_inv P := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).symm_apply_apply P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).apply_symm_apply Q.toSubmodule)
  map_rel_iff' := (Submodule.orderIsoMapComap e).map_rel_iff

private theorem centralCharacter_multiplier_iff
    (χ ω : HeckeCharacter F) (f : ContinuousRationalFunctions F n) :
    determinantMultiplier n χ f ∈ centralCharacterSubrepresentation F n (χ ^ n * ω) ↔
      f ∈ centralCharacterSubrepresentation F n ω := by
  constructor
  · intro hf
    have hp := centralCharacter_determinantMultiplier n χ⁻¹ (χ ^ n * ω) hf
    have hi : (χ⁻¹) ^ n * (χ ^ n * ω) = ω := by
      rw [inv_pow]
      exact inv_mul_cancel_left (χ ^ n) ω
    change determinantMul n χ⁻¹ (determinantMul n χ f) ∈
      centralCharacterSubrepresentation F n ((χ⁻¹) ^ n * (χ ^ n * ω)) at hp
    rw [determinantMul_inv_apply, hi] at hp
    exact hp
  · exact centralCharacter_determinantMultiplier n χ ω

namespace FiniteRealization

variable (S : FiniteRealization F n) (χ : HeckeCharacter F)

local instance heckeFiniteTransportSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Multiplication and inverse multiplication transport all invariant subspaces. -/
def heckeDeterminantTwistSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o
      Subrepresentation (S.heckeDeterminantTwist χ).representation :=
  scalarCovariantSubrepresentationOrderIso S.representation
    (S.heckeDeterminantTwist χ).representation
    ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (S.heckeDeterminantTwistEquiv_representation χ)

@[simp]
theorem heckeDeterminantTwistSubrepresentationOrderIso_toSubmodule
    (P : Subrepresentation S.representation) :
    (S.heckeDeterminantTwistSubrepresentationOrderIso χ P).toSubmodule =
      P.toSubmodule.map (S.heckeDeterminantTwistEquiv χ).toLinearMap := rfl

@[simp]
theorem heckeDeterminantTwist_isIrreducible_iff :
    (S.heckeDeterminantTwist χ).IsIrreducible ↔ S.IsIrreducible :=
  (S.heckeDeterminantTwistSubrepresentationOrderIso χ).isSimpleOrder_iff.symm

/-- Specified central characters are transported on the actual embedded forms. -/
theorem heckeDeterminantTwist_hasCentralCharacter_iff (ω : HeckeCharacter F) :
    (S.heckeDeterminantTwist χ).HasCentralCharacter (χ ^ n * ω) ↔
      S.HasCentralCharacter ω := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (centralCharacter_multiplier_iff χ ω (automorphicToContinuous F n f)).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧
      AutomorphicForms.heckeDeterminantMultiplier n χ g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact centralCharacter_determinantMultiplier n χ ω (hs hg)

theorem heckeDeterminantTwist_hasCentralCharacter (ω : HeckeCharacter F)
    (hS : S.HasCentralCharacter ω) :
    (S.heckeDeterminantTwist χ).HasCentralCharacter (χ ^ n * ω) :=
  (S.heckeDeterminantTwist_hasCentralCharacter_iff χ ω).mpr hS

variable [CompactSpace (AdeleQuotient F)]

/-- Vanishing of the actual constant terms is preserved and reflected. -/
@[simp]
theorem heckeDeterminantTwist_isCuspidal_iff :
    (S.heckeDeterminantTwist χ).IsCuspidal ↔ S.IsCuspidal := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (isCuspidal_determinantMultiplier_iff n χ (automorphicToContinuous F n f)).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧
      AutomorphicForms.heckeDeterminantMultiplier n χ g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact IsCuspidal.determinantMultiplier n χ (hs hg)

end FiniteRealization

namespace LocalRealization

variable {v : FinitePlace F} (S : LocalRealization F n v)
variable (χ : HeckeCharacter F)

local instance heckeLocalTransportSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual local multiplier transports the full invariant-subspace lattice. -/
def heckeDeterminantTwistSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o
      Subrepresentation (S.heckeDeterminantTwist χ).representation :=
  scalarCovariantSubrepresentationOrderIso S.representation
    (S.heckeDeterminantTwist χ).representation
    (χ.finiteLocalDeterminant n v).toMonoidHom
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (S.heckeDeterminantTwistEquiv_representation χ)

@[simp]
theorem heckeDeterminantTwistSubrepresentationOrderIso_toSubmodule
    (P : Subrepresentation S.representation) :
    (S.heckeDeterminantTwistSubrepresentationOrderIso χ P).toSubmodule =
      P.toSubmodule.map (S.heckeDeterminantTwistEquiv χ).toLinearMap := rfl

@[simp]
theorem heckeDeterminantTwist_isIrreducible_iff :
    (S.heckeDeterminantTwist χ).representation.IsIrreducible ↔
      S.representation.IsIrreducible :=
  (S.heckeDeterminantTwistSubrepresentationOrderIso χ).isSimpleOrder_iff.symm

/-- The local subspace retains its global central-character condition on forms. -/
theorem heckeDeterminantTwist_hasCentralCharacter_iff (ω : HeckeCharacter F) :
    (S.heckeDeterminantTwist χ).HasCentralCharacter (χ ^ n * ω) ↔
      S.HasCentralCharacter ω := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (centralCharacter_multiplier_iff χ ω (automorphicToContinuous F n f)).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧
      AutomorphicForms.heckeDeterminantMultiplier n χ g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact centralCharacter_determinantMultiplier n χ ω (hs hg)

theorem heckeDeterminantTwist_hasCentralCharacter (ω : HeckeCharacter F)
    (hS : S.HasCentralCharacter ω) :
    (S.heckeDeterminantTwist χ).HasCentralCharacter (χ ^ n * ω) :=
  (S.heckeDeterminantTwist_hasCentralCharacter_iff χ ω).mpr hS

variable [CompactSpace (AdeleQuotient F)]

@[simp]
theorem heckeDeterminantTwist_isCuspidal_iff :
    (S.heckeDeterminantTwist χ).IsCuspidal ↔ S.IsCuspidal := by
  constructor
  · intro ht f hf
    have hm := ht (Submodule.mem_map_of_mem hf)
    exact (isCuspidal_determinantMultiplier_iff n χ (automorphicToContinuous F n f)).mp hm
  · intro hs f hf
    change ∃ g, g ∈ S.toSubmodule ∧
      AutomorphicForms.heckeDeterminantMultiplier n χ g = f at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact IsCuspidal.determinantMultiplier n χ (hs hg)

end LocalRealization
end Langlands.Automorphic
