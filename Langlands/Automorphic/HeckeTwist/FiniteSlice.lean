import Langlands.Automorphic.DeterminantTwistFiniteSlice
import Langlands.Automorphic.CuspidalFiniteSlice
import Langlands.Automorphic.HeckeTwist.OperatorTwistFiniteComparison
import Langlands.Automorphic.HeckeTwist.FiniteLocalTwist

/-! # Finite slices under multiplication by any Hecke character

For an arbitrary Hecke character `χ`, the image of a finite slice of a cuspidal realization
under multiplication by `χ ∘ det` is a finite slice of the twisted realization.
-/

noncomputable section
universe uF

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (χ : HeckeCharacter F)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

@[simp]
theorem formInclusion_heckeDeterminantTwistEquiv (f : S.Space) :
    (S.heckeDeterminantTwist χ).formInclusion (S.heckeDeterminantTwistEquiv χ f) =
      AutomorphicForms.heckeDeterminantMultiplier n χ (S.formInclusion f) := rfl

/-- Finite restriction and full determinant multiplication give the same form subspace. -/
@[simp]
theorem toFiniteRealization_heckeDeterminantTwist :
    (S.heckeDeterminantTwist χ).toFiniteRealization =
      S.toFiniteRealization.heckeDeterminantTwist χ := by
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := (S.heckeDeterminantTwistEquiv χ).surjective g
    exact ⟨S.formInclusion h, ⟨h, rfl⟩, rfl⟩
  · rintro f ⟨g, hg, rfl⟩
    obtain ⟨h, rfl⟩ := hg
    exact ⟨S.heckeDeterminantTwistEquiv χ h, rfl⟩

end OperatorRealization

namespace CuspidalOperatorRealization.FiniteSlice

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
variable {S : CuspidalOperatorRealization F r} (A : S.FiniteSlice)
variable (χ : HeckeCharacter F)

local instance : AddCommGroup A.subspace.Space := Submodule.addCommGroup _

/-- The actual multiplied slice lies in the full multiplied cuspidal realization. -/
def heckeDeterminantTwist : (S.heckeDeterminantTwist χ).FiniteSlice where
  subspace := A.subspace.heckeDeterminantTwist χ
  le_image := by
    change A.subspace.heckeDeterminantTwist χ ≤
      (S.realization.heckeDeterminantTwist χ).toFiniteRealization
    rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
    exact A.subspace.heckeDeterminantTwist_mono χ A.le_image
  nonzero := (A.subspace.heckeDeterminantTwist_ne_bot_iff χ).mpr A.nonzero

@[simp]
theorem heckeDeterminantTwist_subspace :
    (A.heckeDeterminantTwist χ).subspace = A.subspace.heckeDeterminantTwist χ := rfl

/-- The actual function multiplier continuously identifies the slice with its image. -/
def heckeDeterminantTwistEquiv :
    A.subspace.Space ≃L[ℂ] (A.heckeDeterminantTwist χ).subspace.Space :=
  A.subspace.heckeDeterminantTwistEquiv χ

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv (f : A.subspace.Space) (g : AdelicGL F (r + 1)) :
    evaluate F (r + 1)
        ((A.heckeDeterminantTwist χ).subspace.toContinuous (A.heckeDeterminantTwistEquiv χ f)) g =
      (χ.adelicDeterminant (r + 1) g : ℂ) *
        evaluate F (r + 1) (A.subspace.toContinuous f) g :=
  A.subspace.evaluate_heckeDeterminantTwistEquiv χ f g

/-- The finite action on the multiplied slice is the genuine scalar-twisted action. -/
def heckeDeterminantTwistRepresentationEquiv :
    (Langlands.twist
      ((χ.adelicDeterminant (r + 1)).comp (AdelicGL.ofFinite F (r + 1))).toMonoidHom
      A.subspace.representation).Equiv (A.heckeDeterminantTwist χ).subspace.representation :=
  A.subspace.heckeDeterminantTwistRepresentationEquiv χ

end CuspidalOperatorRealization.FiniteSlice
end Langlands.Automorphic
