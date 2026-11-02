import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison
import Langlands.Automorphic.OperatorDeterminantTwistClasses
import Langlands.Representation.Unitary.Twist

/-! # Positive forms on actual finite-order determinant twists -/

noncomputable section
universe uF uV uW
set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

variable {F : Type uF} [Field F] [NumberField F]

/-- Finite-order Hecke characters have unit modulus on the actual idele classes. -/
theorem HasFiniteOrder.isUnitary {χ : HeckeCharacter F} (hχ : χ.HasFiniteOrder) :
    χ.IsUnitary := by
  obtain ⟨m, hm, hpow⟩ := hχ
  intro x
  have hx : (χ x) ^ m = 1 := by
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun,
      Pi.one_apply] using congrArg (fun η : HeckeCharacter F => η x) hpow
  apply Complex.norm_eq_one_of_pow_eq_one (n := m) _ hm.ne'
  exact congrArg (fun z : ℂˣ => (z : ℂ)) hx

theorem IsUnitary.norm_finiteAdelicDeterminant {χ : HeckeCharacter F}
    (hχ : χ.IsUnitary) (n : ℕ) (g : FiniteAdelicGL F n) :
    ‖(χ.finiteAdelicDeterminant n g : ℂ)‖ = 1 :=
  hχ (ideleClassMap F
    (AdelicGL.determinant F n (AdelicGL.ofFinite F n g)))

theorem IsUnitary.norm_compactAdelicDeterminant {χ : HeckeCharacter F}
    (hχ : χ.IsUnitary) (n : ℕ) (k : standardInfiniteCompact F n) :
    ‖(χ.compactAdelicDeterminant n k : ℂ)‖ = 1 :=
  hχ (ideleClassMap F
    (AdelicGL.determinant F n (AdelicGL.ofInfinite F n k.val)))

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance determinantUnitaryGroup1 : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance determinantUnitaryGroup2 : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance determinantUnitaryGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance determinantUnitaryGroup4 : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance determinantUnitaryGroup5 : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance operatorUnitarySpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

private theorem inverse_operator
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (A : Module.End ℂ V) (B : Module.End ℂ W)
    (he : ∀ v, B (e v) = e (A v)) (w : W) :
    e.symm (B w) = A (e.symm w) := by
  obtain ⟨v, rfl⟩ := e.surjective w
  exact (congrArg e.symm (he v)).trans (e.symm_apply_apply (A v)) |>.trans
    (congrArg A (e.symm_apply_apply v)).symm

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n} (b : S.UnitaryForm)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

private def determinantFiniteForm :
    Langlands.InvariantPositiveForm (S.determinantTwist χ hχ).finiteRepresentation :=
  (b.finiteForm.twist (χ.finiteAdelicDeterminant n).toMonoidHom
    (hχ.isUnitary.norm_finiteAdelicDeterminant n)).ofEquiv
      (S.determinantTwistFiniteEquiv χ hχ).symm

private def determinantCompactForm :
    Langlands.InvariantPositiveForm (S.determinantTwist χ hχ).compactRepresentation :=
  (b.compactForm.twist (χ.compactAdelicDeterminant n).toMonoidHom
    (hχ.isUnitary.norm_compactAdelicDeterminant n)).ofEquiv
      (S.determinantTwistCompactEquiv χ hχ).symm

/-- Transfer the same positive form to the actual determinant-multiplied image.
Finite and compact invariance use unit modulus; genuine real differentiation
intertwines the actual multiplier. -/
def determinantTwist : (S.determinantTwist χ hχ).UnitaryForm where
  finiteForm := determinantFiniteForm b χ hχ
  compact_invariant := (determinantCompactForm b χ hχ).invariant
  real_skew X f g := by
    let e := (S.determinantTwistEquiv χ hχ).toLinearEquiv
    let a := ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)
    have hf := inverse_operator e (S.envelopingAction a)
      ((S.determinantTwist χ hχ).envelopingAction a)
      (S.determinantTwistEquiv_differential χ hχ a) f
    have hg := inverse_operator e (S.envelopingAction a)
      ((S.determinantTwist χ hχ).envelopingAction a)
      (S.determinantTwistEquiv_differential χ hχ a) g
    exact (congrArg₂ (fun u v : S.Space =>
      b.inner u (e.symm g) + b.inner (e.symm f) v) hf hg).trans
        (b.real_skew X (e.symm f) (e.symm g))

@[simp] theorem determinantTwist_inner
    (f g : (S.determinantTwist χ hχ).Space) :
    (b.determinantTwist χ hχ).inner f g =
      b.inner ((S.determinantTwistEquiv χ hχ).symm f)
        ((S.determinantTwistEquiv χ hχ).symm g) := rfl

@[simp] theorem determinantTwist_inner_apply (f g : S.Space) :
    (b.determinantTwist χ hχ).inner
      (S.determinantTwistEquiv χ hχ f) (S.determinantTwistEquiv χ hχ g) =
        b.inner f g := by
  change b.inner ((S.determinantTwistEquiv χ hχ).symm
      (S.determinantTwistEquiv χ hχ f))
    ((S.determinantTwistEquiv χ hχ).symm
      (S.determinantTwistEquiv χ hχ g)) = _
  exact congrArg₂ (fun u v : S.Space => b.inner u v)
    ((S.determinantTwistEquiv χ hχ).symm_apply_apply f)
    ((S.determinantTwistEquiv χ hχ).symm_apply_apply g)

end OperatorRealization.UnitaryForm

namespace OperatorRealization

theorem IsUnitarizable.determinantTwist {S : OperatorRealization F n}
    (hS : S.IsUnitarizable) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (S.determinantTwist χ hχ).IsUnitarizable := by
  obtain ⟨b⟩ := hS
  exact ⟨b.determinantTwist χ hχ⟩

namespace IsoClass

theorem IsUnitarizable.determinantTwist {c : IsoClass F n}
    (hc : c.IsUnitarizable) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (c.determinantTwist χ hχ).IsUnitarizable := by
  induction c using Quotient.inductionOn with
  | h S => exact OperatorRealization.IsUnitarizable.determinantTwist hc χ hχ

theorem determinantTwist_isUnitarizable_iff (c : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (c.determinantTwist χ hχ).IsUnitarizable ↔ c.IsUnitarizable := by
  constructor
  · intro hc
    have hi := hc.determinantTwist χ⁻¹ hχ.inv
    rw [determinantTwist_inv] at hi
    exact hi
  · intro hc
    exact hc.determinantTwist χ hχ

end IsoClass

theorem determinantTwist_isUnitarizable_iff (S : OperatorRealization F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (S.determinantTwist χ hχ).IsUnitarizable ↔ S.IsUnitarizable :=
  IsoClass.determinantTwist_isUnitarizable_iff S.isoClass χ hχ

end OperatorRealization
end Langlands.Automorphic
