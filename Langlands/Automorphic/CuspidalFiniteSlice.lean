import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Nonzero finite invariant subspaces inside actual cuspidal realizations -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

namespace CuspidalOperatorRealization

variable {F} {r : ℕ}

/-- A nonzero actual finite invariant subspace inside the full realization.
No finite irreducibility or factorization is included in this definition. -/
structure FiniteSlice (S : CuspidalOperatorRealization F r) where
  subspace : FiniteRealization F (r + 1)
  le_image : subspace ≤ S.realization.toFiniteRealization
  nonzero : subspace ≠ ⊥

namespace FiniteSlice

variable {S T : CuspidalOperatorRealization F r} (A : S.FiniteSlice)

local instance : AddCommGroup A.subspace.Space := Submodule.addCommGroup _

/-- The whole finite restriction is one available nonzero slice. -/
def whole (S : CuspidalOperatorRealization F r) : S.FiniteSlice where
  subspace := S.realization.toFiniteRealization
  le_image := le_rfl
  nonzero := S.finiteRealization_ne_bot

/-- Nonzeroness is witnessed by an actual form vector. -/
theorem exists_ne_zero : ∃ f : A.subspace.Space, f ≠ 0 := by
  by_contra! h
  apply A.nonzero
  apply le_antisymm ?_ bot_le
  intro f hf
  exact congrArg A.subspace.inclusion (h ⟨f, hf⟩)

/-- A nonzero full-realization vector generates an actual nonzero finite slice. -/
def generated (S : CuspidalOperatorRealization F r) (f : S.Space) (hf : f ≠ 0) :
    S.FiniteSlice where
  subspace := generatedFiniteRealization F (r + 1) (S.realization.formInclusion f)
  le_image := (generatedFiniteRealization_le_iff F (r + 1) _ _).mpr ⟨f, rfl⟩
  nonzero := generatedFiniteRealization_ne_bot F (r + 1) (by
    intro h
    exact hf (S.realization.formInclusion_injective (h.trans (map_zero _).symm)))

/-- Cuspidality is inherited through actual subspace containment. -/
theorem isCuspidal : A.subspace.IsCuspidal :=
  A.le_image.trans S.cuspidal

/-- A prescribed character is inherited only from the actual containing image. -/
theorem hasCentralCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : S.HasCentralCharacter χ) : A.subspace.HasCentralCharacter χ :=
  A.le_image.trans hχ

/-- The inclusion into the entire finite image intertwines the finite action. -/
def inclusion :
    A.subspace.representation.IntertwiningMap S.realization.toFiniteRealization.representation where
  toLinearMap :=
    { toFun := fun f => ⟨f.val, A.le_image f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := by ext; rfl

theorem inclusion_injective : Function.Injective A.inclusion := by
  intro f g h
  exact A.subspace.inclusion_injective
    (congrArg S.realization.toFiniteRealization.inclusion h)

@[simp]
theorem form_inclusion (f : A.subspace.Space) :
    S.realization.toFiniteRealization.inclusion (A.inclusion f) = A.subspace.inclusion f := rfl

variable (e : S.Equivalence T)

/-- Transport a slice vector through the full equivalence and the target form inclusion. -/
def transportMap : FiniteRealizationMap F (r + 1) A.subspace.representation :=
  T.realization.toFiniteRealization.inclusion.comp
    (e.finiteImage.toIntertwiningMap.comp A.inclusion)

theorem transportMap_injective : Function.Injective (A.transportMap e) :=
  T.realization.toFiniteRealization.inclusion_injective.comp
    (e.finiteImage.injective.comp A.inclusion_injective)

/-- The actual image remains a nonzero finite invariant subspace of the target. -/
def transport : T.FiniteSlice where
  subspace := finiteRealizationImage F (r + 1) (A.transportMap e)
  le_image := by
    rintro f ⟨x, rfl⟩
    exact (e.finiteImage (A.inclusion x)).property
  nonzero := by
    intro h
    obtain ⟨f, hf⟩ := A.exists_ne_zero
    have hm : A.transportMap e f ∈ finiteRealizationImage F (r + 1) (A.transportMap e) :=
      ⟨f, rfl⟩
    rw [h] at hm
    change A.transportMap e f = 0 at hm
    exact hf (A.transportMap_injective e (hm.trans (map_zero _).symm))

/-- The transported actual image is equivalent to the original finite slice. -/
def transportEquiv : A.subspace.representation.Equiv (A.transport e).subspace.representation :=
  finiteRealizationImageEquiv F (r + 1) (A.transportMap e) (A.transportMap_injective e)

@[simp]
theorem transportEquiv_inclusion (f : A.subspace.Space) :
    (A.transport e).subspace.inclusion (A.transportEquiv e f) = A.transportMap e f := rfl

/-- Finite class is preserved by the constructed transport. -/
theorem transport_isoClass : (A.transport e).subspace.isoClass = A.subspace.isoClass :=
  ((A.transport e).subspace.isoClass_eq_iff A.subspace).mpr ⟨(A.transportEquiv e).symm⟩

/-- Every transported vector is cuspidal because it lies in the target cusp image. -/
theorem transport_isCuspidal : (A.transport e).subspace.IsCuspidal :=
  (A.transport e).isCuspidal

end FiniteSlice
end CuspidalOperatorRealization
end Langlands.Automorphic
