import Langlands.Automorphic.AutomorphicDeterminantMultiplier
import Langlands.Automorphic.LocalRealization
import Langlands.Representation.Twist.Definitions

/-! # Actual determinant images of finite and local automorphic realizations -/

noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-- The actual adelic determinant character restricted to one finite local group. -/
def finiteLocalDeterminant (χ : HeckeCharacter F) (v : FinitePlace F) :
    FiniteLocalGL F n v →ₜ* ℂˣ :=
  ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).comp
    (FiniteAdelicGL.localInclusion F n v)

@[simp]
theorem finiteLocalDeterminant_apply (χ : HeckeCharacter F) (v : FinitePlace F)
    (g : FiniteLocalGL F n v) :
    χ.finiteLocalDeterminant n v g =
      χ.adelicDeterminant n
        (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v g)) := rfl

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance finiteLocalTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance finiteLocalTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteLocalTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteLocalTwistFormsGroup (n : ℕ) :
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

theorem localRightAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (v : FinitePlace F)
    (g : FiniteLocalGL F n v) (f : AutomorphicForms F n) :
    automorphicLocalRightAction F n v g (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.finiteLocalDeterminant n v g : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ
          (automorphicLocalRightAction F n v g f) :=
  finiteRightAction_determinantMultiplier n χ hχ (FiniteAdelicGL.localInclusion F n v g) f

end AutomorphicForms

namespace FiniteRealization

variable (S : FiniteRealization F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance finiteImageTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual multiplied form subspace, with finite adelic invariance proved. -/
def determinantTwist : FiniteRealization F n :=
  scalarImage (automorphicFiniteRightAction F n)
    ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
    (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).toLinearEquiv
    (AutomorphicForms.finiteRightAction_determinantMultiplier n χ hχ) S

/-- Multiplication itself, continuously identifying the source with its actual image. -/
def determinantTwistEquiv : S.Space ≃L[ℂ] (S.determinantTwist χ hχ).Space :=
  (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _ rfl

@[simp]
theorem determinantTwistEquiv_val (f : S.Space) :
    (S.determinantTwistEquiv χ hχ f).val =
      AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

theorem determinantTwistEquiv_representation (g : FiniteAdelicGL F n) (f : S.Space) :
    (S.determinantTwist χ hχ).representation g (S.determinantTwistEquiv χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n g) : ℂ) •
        S.determinantTwistEquiv χ hχ (S.representation g f) := by
  apply Subtype.ext
  exact AutomorphicForms.finiteRightAction_determinantMultiplier n χ hχ g f.val

/-- A genuine equivariant comparison with the existing scalar twist. -/
def determinantTwistRepresentationEquiv :
    (Langlands.twist
      ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
      S.representation).Equiv (S.determinantTwist χ hχ).representation :=
  scalarImageRepresentationEquiv S.representation (S.determinantTwist χ hχ).representation
    ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
    (S.determinantTwistEquiv χ hχ).toLinearEquiv
    (S.determinantTwistEquiv_representation χ hχ)

@[simp]
theorem determinantTwistRepresentationEquiv_apply (f : S.Space) :
    S.determinantTwistRepresentationEquiv χ hχ f = S.determinantTwistEquiv χ hχ f := rfl

@[simp]
theorem toContinuous_determinantTwistEquiv (f : S.Space) :
    (S.determinantTwist χ hχ).toContinuous (S.determinantTwistEquiv χ hχ f) =
      determinantMultiplier n χ (S.toContinuous f) := rfl

@[simp]
theorem evaluate_determinantTwistEquiv (f : S.Space) (g : AdelicGL F n) :
    evaluate F n ((S.determinantTwist χ hχ).toContinuous (S.determinantTwistEquiv χ hχ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (S.toContinuous f) g := rfl

@[simp]
theorem evaluate_determinantTwistEquiv_symm
    (f : (S.determinantTwist χ hχ).Space) (g : AdelicGL F n) :
    evaluate F n (S.toContinuous ((S.determinantTwistEquiv χ hχ).symm f)) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n ((S.determinantTwist χ hχ).toContinuous f) g := rfl

@[simp]
theorem determinantTwist_eq_bot_iff :
    S.determinantTwist χ hχ = ⊥ ↔ S = ⊥ :=
  scalarImage_eq_bot_iff _ _ _ _ S

theorem determinantTwist_ne_bot_iff :
    S.determinantTwist χ hχ ≠ ⊥ ↔ S ≠ ⊥ :=
  not_congr (S.determinantTwist_eq_bot_iff χ hχ)

theorem determinantTwist_mono {T : FiniteRealization F n} (hST : S ≤ T) :
    S.determinantTwist χ hχ ≤ T.determinantTwist χ hχ :=
  Submodule.map_mono hST

end FiniteRealization

namespace LocalRealization

variable {v : FinitePlace F} (S : LocalRealization F n v)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance localImageTwistSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual multiplied form subspace, with invariance under this local group proved. -/
def determinantTwist : LocalRealization F n v :=
  scalarImage (automorphicLocalRightAction F n v)
    (χ.finiteLocalDeterminant n v).toMonoidHom
    (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).toLinearEquiv
    (AutomorphicForms.localRightAction_determinantMultiplier χ hχ v) S

def determinantTwistEquiv : S.Space ≃L[ℂ] (S.determinantTwist χ hχ).Space :=
  (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _ rfl

@[simp]
theorem determinantTwistEquiv_val (f : S.Space) :
    (S.determinantTwistEquiv χ hχ f).val =
      AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

theorem determinantTwistEquiv_representation (g : FiniteLocalGL F n v) (f : S.Space) :
    (S.determinantTwist χ hχ).representation g (S.determinantTwistEquiv χ hχ f) =
      (χ.finiteLocalDeterminant n v g : ℂ) •
        S.determinantTwistEquiv χ hχ (S.representation g f) := by
  apply Subtype.ext
  exact AutomorphicForms.localRightAction_determinantMultiplier χ hχ v g f.val

def determinantTwistRepresentationEquiv :
    (Langlands.twist (χ.finiteLocalDeterminant n v).toMonoidHom S.representation).Equiv
      (S.determinantTwist χ hχ).representation :=
  scalarImageRepresentationEquiv S.representation (S.determinantTwist χ hχ).representation
    (χ.finiteLocalDeterminant n v).toMonoidHom
    (S.determinantTwistEquiv χ hχ).toLinearEquiv
    (S.determinantTwistEquiv_representation χ hχ)

@[simp]
theorem determinantTwistRepresentationEquiv_apply (f : S.Space) :
    S.determinantTwistRepresentationEquiv χ hχ f = S.determinantTwistEquiv χ hχ f := rfl

@[simp]
theorem toContinuous_determinantTwistEquiv (f : S.Space) :
    (S.determinantTwist χ hχ).toContinuous (S.determinantTwistEquiv χ hχ f) =
      determinantMultiplier n χ (S.toContinuous f) := rfl

@[simp]
theorem evaluate_determinantTwistEquiv (f : S.Space) (g : AdelicGL F n) :
    evaluate F n ((S.determinantTwist χ hχ).toContinuous (S.determinantTwistEquiv χ hχ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (S.toContinuous f) g := rfl

@[simp]
theorem evaluate_determinantTwistEquiv_symm
    (f : (S.determinantTwist χ hχ).Space) (g : AdelicGL F n) :
    evaluate F n (S.toContinuous ((S.determinantTwistEquiv χ hχ).symm f)) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n ((S.determinantTwist χ hχ).toContinuous f) g := rfl

@[simp]
theorem determinantTwist_eq_bot_iff :
    S.determinantTwist χ hχ = ⊥ ↔ S = ⊥ :=
  scalarImage_eq_bot_iff _ _ _ _ S

theorem determinantTwist_ne_bot_iff :
    S.determinantTwist χ hχ ≠ ⊥ ↔ S ≠ ⊥ :=
  not_congr (S.determinantTwist_eq_bot_iff χ hχ)

theorem determinantTwist_mono {T : LocalRealization F n v} (hST : S ≤ T) :
    S.determinantTwist χ hχ ≤ T.determinantTwist χ hχ :=
  Submodule.map_mono hST

end LocalRealization

/-- Local restriction and actual image multiplication give the same embedded subspace. -/
@[simp]
theorem FiniteRealization.toLocal_determinantTwist
    (S : FiniteRealization F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (v : FinitePlace F) :
    (S.determinantTwist χ hχ).toLocal F n v = (S.toLocal F n v).determinantTwist χ hχ :=
  Subrepresentation.toSubmodule_injective rfl

end Langlands.Automorphic
