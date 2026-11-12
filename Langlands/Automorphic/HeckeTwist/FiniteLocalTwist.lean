import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Automorphic.HeckeTwist.AutomorphicMultiplier
import Langlands.Automorphic.LocalRealization
import Langlands.Representation.Twist.Definitions

/-! # Images of finite and local automorphic realizations under any Hecke multiplier

For an arbitrary Hecke character `χ`, multiplication by `χ ∘ det` carries finite and local
automorphic realizations to realizations whose representations are the scalar twists by
the finite, respectively local, determinant character of `χ`.
-/

noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance heckeFiniteLocalTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeFiniteLocalTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeFiniteLocalTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeFiniteLocalTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

private def scalarImage
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (η : G →* ℂˣ) (e : V ≃ₗ[ℂ] V)
    (hc : ∀ g f, ρ g (e f) = (η g : ℂ) • e (ρ g f))
    (S : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule g _ hf := by
    change ∃ f, f ∈ S.toSubmodule ∧ e f = _ at hf
    obtain ⟨f, hf, rfl⟩ := hf
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (S.apply_mem_toSubmodule g hf))

private def scalarImageRepresentationEquiv
    {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (η : G →* ℂˣ) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ g f, τ g (e f) = (η g : ℂ) • e (ρ g f)) :
    (Langlands.twist η ρ).Equiv τ :=
  Representation.Equiv.mk e (fun g => by
    apply LinearMap.ext
    intro f
    change e ((η g : ℂ) • ρ g f) = τ g (e f)
    rw [e.map_smul]
    exact (hc g f).symm)

private theorem scalarImage_eq_bot_iff
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (η : G →* ℂˣ) (e : V ≃ₗ[ℂ] V)
    (hc : ∀ g f, ρ g (e f) = (η g : ℂ) • e (ρ g f))
    (S : Subrepresentation ρ) :
    scalarImage ρ η e hc S = ⊥ ↔ S = ⊥ := by
  constructor
  · intro h
    apply le_antisymm ?_ bot_le
    intro f hf
    have hm : e f ∈ scalarImage ρ η e hc S := Submodule.mem_map_of_mem hf
    rw [h] at hm
    exact e.injective (hm.trans e.map_zero.symm)
  · intro h
    subst S
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _

namespace AutomorphicForms

theorem localRightAction_heckeDeterminantMultiplier
    (χ : HeckeCharacter F) (v : FinitePlace F)
    (g : FiniteLocalGL F n v) (f : AutomorphicForms F n) :
    automorphicLocalRightAction F n v g (heckeDeterminantMultiplier n χ f) =
      (χ.finiteLocalDeterminant n v g : ℂ) •
        heckeDeterminantMultiplier n χ
          (automorphicLocalRightAction F n v g f) :=
  finiteRightAction_heckeDeterminantMultiplier n χ (FiniteAdelicGL.localInclusion F n v g) f

end AutomorphicForms

namespace FiniteRealization

variable (S : FiniteRealization F n) (χ : HeckeCharacter F)

local instance heckeFiniteImageTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual multiplied form subspace, with finite adelic invariance proved. -/
def heckeDeterminantTwist : FiniteRealization F n :=
  scalarImage (automorphicFiniteRightAction F n)
    ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
    (AutomorphicForms.heckeDeterminantMultiplier n χ).toLinearEquiv
    (AutomorphicForms.finiteRightAction_heckeDeterminantMultiplier n χ) S

/-- Multiplication itself, continuously identifying the source with its actual image. -/
def heckeDeterminantTwistEquiv : S.Space ≃L[ℂ] (S.heckeDeterminantTwist χ).Space :=
  (AutomorphicForms.heckeDeterminantMultiplier n χ).ofSubmodules _ _ rfl

@[simp]
theorem heckeDeterminantTwistEquiv_val (f : S.Space) :
    (S.heckeDeterminantTwistEquiv χ f).val =
      AutomorphicForms.heckeDeterminantMultiplier n χ f.val := rfl

theorem heckeDeterminantTwistEquiv_representation (g : FiniteAdelicGL F n) (f : S.Space) :
    (S.heckeDeterminantTwist χ).representation g (S.heckeDeterminantTwistEquiv χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n g) : ℂ) •
        S.heckeDeterminantTwistEquiv χ (S.representation g f) := by
  apply Subtype.ext
  exact AutomorphicForms.finiteRightAction_heckeDeterminantMultiplier n χ g f.val

/-- A genuine equivariant comparison with the existing scalar twist. -/
def heckeDeterminantTwistRepresentationEquiv :
    (Langlands.twist
      ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
      S.representation).Equiv (S.heckeDeterminantTwist χ).representation :=
  scalarImageRepresentationEquiv S.representation (S.heckeDeterminantTwist χ).representation
    ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (S.heckeDeterminantTwistEquiv_representation χ)

@[simp]
theorem heckeDeterminantTwistRepresentationEquiv_apply (f : S.Space) :
    S.heckeDeterminantTwistRepresentationEquiv χ f = S.heckeDeterminantTwistEquiv χ f := rfl

@[simp]
theorem toContinuous_heckeDeterminantTwistEquiv (f : S.Space) :
    (S.heckeDeterminantTwist χ).toContinuous (S.heckeDeterminantTwistEquiv χ f) =
      determinantMultiplier n χ (S.toContinuous f) := rfl

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv (f : S.Space) (g : AdelicGL F n) :
    evaluate F n ((S.heckeDeterminantTwist χ).toContinuous (S.heckeDeterminantTwistEquiv χ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (S.toContinuous f) g := rfl

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv_symm
    (f : (S.heckeDeterminantTwist χ).Space) (g : AdelicGL F n) :
    evaluate F n (S.toContinuous ((S.heckeDeterminantTwistEquiv χ).symm f)) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n ((S.heckeDeterminantTwist χ).toContinuous f) g := rfl

@[simp]
theorem heckeDeterminantTwist_eq_bot_iff :
    S.heckeDeterminantTwist χ = ⊥ ↔ S = ⊥ :=
  scalarImage_eq_bot_iff _ _ _ _ S

theorem heckeDeterminantTwist_ne_bot_iff :
    S.heckeDeterminantTwist χ ≠ ⊥ ↔ S ≠ ⊥ :=
  not_congr (S.heckeDeterminantTwist_eq_bot_iff χ)

theorem heckeDeterminantTwist_mono {T : FiniteRealization F n} (hST : S ≤ T) :
    S.heckeDeterminantTwist χ ≤ T.heckeDeterminantTwist χ :=
  Submodule.map_mono hST

end FiniteRealization

namespace LocalRealization

variable {v : FinitePlace F} (S : LocalRealization F n v)
variable (χ : HeckeCharacter F)

local instance heckeLocalImageTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual multiplied form subspace, with invariance under this local group proved. -/
def heckeDeterminantTwist : LocalRealization F n v :=
  scalarImage (automorphicLocalRightAction F n v)
    (χ.finiteLocalDeterminant n v).toMonoidHom
    (AutomorphicForms.heckeDeterminantMultiplier n χ).toLinearEquiv
    (AutomorphicForms.localRightAction_heckeDeterminantMultiplier χ v) S

def heckeDeterminantTwistEquiv : S.Space ≃L[ℂ] (S.heckeDeterminantTwist χ).Space :=
  (AutomorphicForms.heckeDeterminantMultiplier n χ).ofSubmodules _ _ rfl

@[simp]
theorem heckeDeterminantTwistEquiv_val (f : S.Space) :
    (S.heckeDeterminantTwistEquiv χ f).val =
      AutomorphicForms.heckeDeterminantMultiplier n χ f.val := rfl

theorem heckeDeterminantTwistEquiv_representation (g : FiniteLocalGL F n v) (f : S.Space) :
    (S.heckeDeterminantTwist χ).representation g (S.heckeDeterminantTwistEquiv χ f) =
      (χ.finiteLocalDeterminant n v g : ℂ) •
        S.heckeDeterminantTwistEquiv χ (S.representation g f) := by
  apply Subtype.ext
  exact AutomorphicForms.localRightAction_heckeDeterminantMultiplier χ v g f.val

def heckeDeterminantTwistRepresentationEquiv :
    (Langlands.twist (χ.finiteLocalDeterminant n v).toMonoidHom S.representation).Equiv
      (S.heckeDeterminantTwist χ).representation :=
  scalarImageRepresentationEquiv S.representation (S.heckeDeterminantTwist χ).representation
    (χ.finiteLocalDeterminant n v).toMonoidHom
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (S.heckeDeterminantTwistEquiv_representation χ)

@[simp]
theorem heckeDeterminantTwistRepresentationEquiv_apply (f : S.Space) :
    S.heckeDeterminantTwistRepresentationEquiv χ f = S.heckeDeterminantTwistEquiv χ f := rfl

@[simp]
theorem toContinuous_heckeDeterminantTwistEquiv (f : S.Space) :
    (S.heckeDeterminantTwist χ).toContinuous (S.heckeDeterminantTwistEquiv χ f) =
      determinantMultiplier n χ (S.toContinuous f) := rfl

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv (f : S.Space) (g : AdelicGL F n) :
    evaluate F n ((S.heckeDeterminantTwist χ).toContinuous (S.heckeDeterminantTwistEquiv χ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (S.toContinuous f) g := rfl

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv_symm
    (f : (S.heckeDeterminantTwist χ).Space) (g : AdelicGL F n) :
    evaluate F n (S.toContinuous ((S.heckeDeterminantTwistEquiv χ).symm f)) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n ((S.heckeDeterminantTwist χ).toContinuous f) g := rfl

@[simp]
theorem heckeDeterminantTwist_eq_bot_iff :
    S.heckeDeterminantTwist χ = ⊥ ↔ S = ⊥ :=
  scalarImage_eq_bot_iff _ _ _ _ S

theorem heckeDeterminantTwist_ne_bot_iff :
    S.heckeDeterminantTwist χ ≠ ⊥ ↔ S ≠ ⊥ :=
  not_congr (S.heckeDeterminantTwist_eq_bot_iff χ)

theorem heckeDeterminantTwist_mono {T : LocalRealization F n v} (hST : S ≤ T) :
    S.heckeDeterminantTwist χ ≤ T.heckeDeterminantTwist χ :=
  Submodule.map_mono hST

end LocalRealization

/-- Local restriction and actual image multiplication give the same embedded subspace. -/
@[simp]
theorem FiniteRealization.toLocal_heckeDeterminantTwist
    (S : FiniteRealization F n) (χ : HeckeCharacter F)
    (v : FinitePlace F) :
    (S.heckeDeterminantTwist χ).toLocal F n v = (S.toLocal F n v).heckeDeterminantTwist χ :=
  Subrepresentation.toSubmodule_injective rfl

end Langlands.Automorphic
