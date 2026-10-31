import Langlands.Automorphic.OperatorDeterminantTwist
import Langlands.Representation.Twist.Definitions

/-! # The actual finite and compact representations of determinant-twisted realizations -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-- The actual determinant character restricted to the finite adelic group. -/
def finiteAdelicDeterminant (χ : HeckeCharacter F) : FiniteAdelicGL F n →ₜ* ℂˣ :=
  (χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)

/-- The actual determinant character restricted to the standard infinite compact. -/
def compactAdelicDeterminant (χ : HeckeCharacter F) :
    standardInfiniteCompact F n →ₜ* ℂˣ where
  toMonoidHom := ((χ.adelicDeterminant n).toMonoidHom.comp
    (AdelicGL.ofInfinite F n).toMonoidHom).comp (standardInfiniteCompact F n).subtype
  continuous_toFun := ((χ.adelicDeterminant n).continuous.comp
    (AdelicGL.ofInfinite F n).continuous).comp continuous_subtype_val

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance twistComparisonRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance twistComparisonContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance twistComparisonFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance twistComparisonFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance twistComparisonStableGroup (n : ℕ) :
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

variable (S : OperatorRealization F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance twistComparisonSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual finite action on the image twist is the existing scalar twist of the source. -/
def determinantTwistFiniteEquiv :
    (Langlands.twist (χ.finiteAdelicDeterminant n).toMonoidHom S.finiteRepresentation).Equiv
      (S.determinantTwist χ hχ).finiteRepresentation :=
  scalarCovarianceEquiv S.finiteRepresentation (S.determinantTwist χ hχ).finiteRepresentation
    (χ.finiteAdelicDeterminant n).toMonoidHom
    (S.determinantTwistEquiv χ hχ).toLinearEquiv (S.determinantTwistEquiv_finite χ hχ)

/-- The actual standard compact action has the analogous genuine scalar-twist equivalence. -/
def determinantTwistCompactEquiv :
    (Langlands.twist (χ.compactAdelicDeterminant n).toMonoidHom S.compactRepresentation).Equiv
      (S.determinantTwist χ hχ).compactRepresentation :=
  scalarCovarianceEquiv S.compactRepresentation (S.determinantTwist χ hχ).compactRepresentation
    (χ.compactAdelicDeterminant n).toMonoidHom
    (S.determinantTwistEquiv χ hχ).toLinearEquiv (S.determinantTwistEquiv_compact χ hχ)

/-- The equivalence also identifies the existing actual finite form images. -/
def determinantTwistFiniteImageEquiv :
    (Langlands.twist (χ.finiteAdelicDeterminant n).toMonoidHom
      S.toFiniteRealization.representation).Equiv
        (S.determinantTwist χ hχ).toFiniteRealization.representation :=
  (Langlands.twistEquiv (χ.finiteAdelicDeterminant n).toMonoidHom S.finiteEquiv).symm.trans
    ((S.determinantTwistFiniteEquiv χ hχ).trans (S.determinantTwist χ hχ).finiteEquiv)

@[simp]
theorem determinantTwistFiniteEquiv_apply (f : S.Space) :
    S.determinantTwistFiniteEquiv χ hχ f = S.determinantTwistEquiv χ hχ f := rfl

@[simp]
theorem determinantTwistCompactEquiv_apply (f : S.Space) :
    S.determinantTwistCompactEquiv χ hχ f = S.determinantTwistEquiv χ hχ f := rfl

@[simp]
theorem determinantTwistFiniteImageEquiv_apply (f : S.Space) :
    S.determinantTwistFiniteImageEquiv χ hχ (S.finiteEquiv f) =
      (S.determinantTwist χ hχ).finiteEquiv (S.determinantTwistEquiv χ hχ f) := by
  change (S.determinantTwist χ hχ).finiteEquiv
      (S.determinantTwistEquiv χ hχ (S.finiteEquiv.symm (S.finiteEquiv f))) = _
  exact congrArg (fun v : S.Space =>
    (S.determinantTwist χ hχ).finiteEquiv (S.determinantTwistEquiv χ hχ v))
      (Representation.Equiv.symm_apply_apply S.finiteEquiv f)

end OperatorRealization
end Langlands.Automorphic
