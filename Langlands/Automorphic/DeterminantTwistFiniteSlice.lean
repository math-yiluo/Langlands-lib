import Langlands.Automorphic.CuspidalFiniteSlice
import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison
import Langlands.Automorphic.FiniteLocalDeterminantTwist

/-! # Actual finite slices under full determinant multiplication -/

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

variable (S : OperatorRealization F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

@[simp]
theorem formInclusion_determinantTwistEquiv (f : S.Space) :
    (S.determinantTwist χ hχ).formInclusion (S.determinantTwistEquiv χ hχ f) =
      AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ (S.formInclusion f) := rfl

/-- Finite restriction and full determinant multiplication give the same form subspace. -/
@[simp]
theorem toFiniteRealization_determinantTwist :
    (S.determinantTwist χ hχ).toFiniteRealization =
      S.toFiniteRealization.determinantTwist χ hχ := by
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := (S.determinantTwistEquiv χ hχ).surjective g
    exact ⟨S.formInclusion h, ⟨h, rfl⟩, rfl⟩
  · rintro f ⟨g, hg, rfl⟩
    obtain ⟨h, rfl⟩ := hg
    exact ⟨S.determinantTwistEquiv χ hχ h, rfl⟩

end OperatorRealization

namespace CuspidalOperatorRealization.FiniteSlice

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
variable {S : CuspidalOperatorRealization F r} (A : S.FiniteSlice)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance : AddCommGroup A.subspace.Space := Submodule.addCommGroup _

/-- The actual multiplied slice lies in the full multiplied cuspidal realization. -/
def determinantTwist : (S.determinantTwist χ hχ).FiniteSlice where
  subspace := A.subspace.determinantTwist χ hχ
  le_image := by
    change A.subspace.determinantTwist χ hχ ≤
      (S.realization.determinantTwist χ hχ).toFiniteRealization
    rw [OperatorRealization.toFiniteRealization_determinantTwist]
    exact A.subspace.determinantTwist_mono χ hχ A.le_image
  nonzero := (A.subspace.determinantTwist_ne_bot_iff χ hχ).mpr A.nonzero

@[simp]
theorem determinantTwist_subspace :
    (A.determinantTwist χ hχ).subspace = A.subspace.determinantTwist χ hχ := rfl

/-- The actual function multiplier continuously identifies the slice with its image. -/
def determinantTwistEquiv :
    A.subspace.Space ≃L[ℂ] (A.determinantTwist χ hχ).subspace.Space :=
  A.subspace.determinantTwistEquiv χ hχ

@[simp]
theorem evaluate_determinantTwistEquiv (f : A.subspace.Space) (g : AdelicGL F (r + 1)) :
    evaluate F (r + 1)
        ((A.determinantTwist χ hχ).subspace.toContinuous (A.determinantTwistEquiv χ hχ f)) g =
      (χ.adelicDeterminant (r + 1) g : ℂ) *
        evaluate F (r + 1) (A.subspace.toContinuous f) g :=
  A.subspace.evaluate_determinantTwistEquiv χ hχ f g

/-- The finite action on the multiplied slice is the genuine scalar-twisted action. -/
def determinantTwistRepresentationEquiv :
    (Langlands.twist
      ((χ.adelicDeterminant (r + 1)).comp (AdelicGL.ofFinite F (r + 1))).toMonoidHom
      A.subspace.representation).Equiv (A.determinantTwist χ hχ).subspace.representation :=
  A.subspace.determinantTwistRepresentationEquiv χ hχ

end CuspidalOperatorRealization.FiniteSlice
end Langlands.Automorphic
