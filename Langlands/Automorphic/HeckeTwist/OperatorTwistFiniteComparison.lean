import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison
import Langlands.Automorphic.HeckeTwist.OperatorTwist
import Langlands.Representation.Twist.Definitions

/-! # Finite and compact representations of Hecke-twisted realizations

For an arbitrary Hecke character `χ`, the finite and standard compact representations of
the twisted realization are the scalar twists of those of the source by `χ ∘ det`.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance heckeTwistComparisonRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeTwistComparisonContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTwistComparisonFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTwistComparisonFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeTwistComparisonStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

private def scalarCovarianceEquiv
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

namespace OperatorRealization

variable (S : OperatorRealization F n) (χ : HeckeCharacter F)

local instance heckeTwistComparisonSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual finite action on the image twist is the existing scalar twist of the source. -/
def heckeDeterminantTwistFiniteEquiv :
    (Langlands.twist (χ.finiteAdelicDeterminant n).toMonoidHom S.finiteRepresentation).Equiv
      (S.heckeDeterminantTwist χ).finiteRepresentation :=
  scalarCovarianceEquiv S.finiteRepresentation (S.heckeDeterminantTwist χ).finiteRepresentation
    (χ.finiteAdelicDeterminant n).toMonoidHom
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv (S.heckeDeterminantTwistEquiv_finite χ)

/-- The actual standard compact action has the analogous genuine scalar-twist equivalence. -/
def heckeDeterminantTwistCompactEquiv :
    (Langlands.twist (χ.compactAdelicDeterminant n).toMonoidHom S.compactRepresentation).Equiv
      (S.heckeDeterminantTwist χ).compactRepresentation :=
  scalarCovarianceEquiv S.compactRepresentation (S.heckeDeterminantTwist χ).compactRepresentation
    (χ.compactAdelicDeterminant n).toMonoidHom
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv (S.heckeDeterminantTwistEquiv_compact χ)

/-- The equivalence also identifies the existing actual finite form images. -/
def heckeDeterminantTwistFiniteImageEquiv :
    (Langlands.twist (χ.finiteAdelicDeterminant n).toMonoidHom
      S.toFiniteRealization.representation).Equiv
        (S.heckeDeterminantTwist χ).toFiniteRealization.representation :=
  (Langlands.twistEquiv (χ.finiteAdelicDeterminant n).toMonoidHom S.finiteEquiv).symm.trans
    ((S.heckeDeterminantTwistFiniteEquiv χ).trans (S.heckeDeterminantTwist χ).finiteEquiv)

@[simp]
theorem heckeDeterminantTwistFiniteEquiv_apply (f : S.Space) :
    S.heckeDeterminantTwistFiniteEquiv χ f = S.heckeDeterminantTwistEquiv χ f := rfl

@[simp]
theorem heckeDeterminantTwistCompactEquiv_apply (f : S.Space) :
    S.heckeDeterminantTwistCompactEquiv χ f = S.heckeDeterminantTwistEquiv χ f := rfl

@[simp]
theorem heckeDeterminantTwistFiniteImageEquiv_apply (f : S.Space) :
    S.heckeDeterminantTwistFiniteImageEquiv χ (S.finiteEquiv f) =
      (S.heckeDeterminantTwist χ).finiteEquiv (S.heckeDeterminantTwistEquiv χ f) := by
  change (S.heckeDeterminantTwist χ).finiteEquiv
      (S.heckeDeterminantTwistEquiv χ (S.finiteEquiv.symm (S.finiteEquiv f))) = _
  exact congrArg (fun v : S.Space =>
    (S.heckeDeterminantTwist χ).finiteEquiv (S.heckeDeterminantTwistEquiv χ v))
      (Representation.Equiv.symm_apply_apply S.finiteEquiv f)

end OperatorRealization
end Langlands.Automorphic
