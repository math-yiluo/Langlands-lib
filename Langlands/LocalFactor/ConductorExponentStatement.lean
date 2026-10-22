import Langlands.LocalFactor.CommonClosureWeilDeligne
import Langlands.LocalFactor.Ramification.InertiaPresentation
import Langlands.VirtualRepresentation.ExactTensor

/-!
# Conductor exponents of supplied local-constant systems

Tate's (3.4.5), (3.4.6) and (4.1.6) and Deligne's (5.5.1)–(5.5.3), for the
conditional common-closure values of a supplied local-constant system, at the
bottom intermediate field of the closure. There the fixing subgroup is the whole
local Weil group, and the Artin conductor is read off from every actual
finite-inertia presentation, with surjectivity of the restriction explicit.
These are propositions; no system, presentation or conductor law is constructed.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.ConductorExponent

open CommonClosure CommonClosureSpectral Weil.Local
open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The base field itself, as the bottom intermediate field of the closure. -/
def base : Extension F := ⟨⊥, inferInstance⟩

/-- Every element of the actual local Weil group fixes the bottom field. -/
theorem mem_weilSubgroup_base (w : localWeilGroup F) : w ∈ weilSubgroup F (base F) := by
  change Weil.projection (localResidueDegree F) w ∈
    (⊥ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_bot]
  exact Subgroup.mem_top _

/-- The local Weil group, mapped identically onto the fixing subgroup of the base. -/
def baseInclusion : localWeilGroup F →ₜ* weilSubgroup F (base F) where
  toFun w := ⟨w, mem_weilSubgroup_base F w⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk _

/-- The exact virtual class of a genuine continuous representation of the base. -/
abbrev baseClass (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) : Virtual.{uF, uV} F (base F) :=
  ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F (base F)) ⟨A, hA⟩

/-- Actual finite-inertia presentations of the same action on the local Weil group. -/
abbrev Presentation (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F))) :=
  Ramification.Padic.FiniteInertiaPresentation F
    (FiniteRepresentation.restrict (baseInclusion F).toMonoidHom A)

/-- Tate's `n(ψ)` on the base field: the largest `n` with `ψ(π^(-n) O) = 1`. -/
abbrev additiveConductor (ψ : AdditiveCharacter F (base F)) : ℤ :=
  (fieldData F (base F)).additiveConductor ψ

/-- Tate (3.4.5) and Deligne (5.5.2): `ε(V ω_s) = ε(V) q^(-(a(V) + n(ψ) dim V) s)`
for a genuine continuous `V`, with `a(V)` computed at any actual presentation. -/
def SpectralConductorStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) (P : Presentation.{uF, uV} F A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension))
    (s : ℂ),
    (conditionalDeligneValue F e ε hε (base F) ψ μ (baseClass F A hA) s : ℂ) =
      (conditionalDeligneValue F e ε hε (base F) ψ μ (baseClass F A hA) 0 : ℂ) *
        (baseCardinality F : ℂ) ^
          (-(((P.artinConductor hsurj : ℚ) : ℂ) +
              (additiveConductor F ψ : ℂ) * (A.rank : ℂ)) * s)

/-- Deligne (5.5.1): for an unramified quasi-character `χ` of the base field and
any `a` of valuation `a(V) + n(ψ) dim V`, `ε(V χ) = ε(V) χ(a)`. -/
def UnramifiedCharacterStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) (P : Presentation.{uF, uV} F A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension))
    (χ : FieldCharacter F (base F)),
    (∀ u : (base F).fieldˣ,
      (fieldData F (base F)).discreteValuation (u : (base F).field) = 1 → χ u = 1) →
    ∀ (m : ℤ), (m : ℚ) = P.artinConductor hsurj + (additiveConductor F ψ : ℚ) * A.rank →
    ∀ (a : (base F).fieldˣ),
      (fieldData F (base F)).discreteValuation (a : (base F).field) = WithZero.exp (-m) →
    ∀ s : ℂ,
      conditionalDeligneValue F e ε hε (base F) ψ μ
          (ExactGrothendieckGroup.continuousTensorSame (baseClass F A hA)
            (characterClass F e (base F) χ)) s =
        conditionalDeligneValue F e ε hε (base F) ψ μ (baseClass F A hA) s * χ a

/-- Tate (3.4.6) and Deligne (5.5.3): for `W` unramified,
`ε(V ⊗ W) = ε(V)^(dim W) · det W(Φ)^(a(V) + n(ψ) dim V)`, `Φ` a geometric Frobenius. -/
def UnramifiedTensorStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) (P : Presentation.{uF, uV} F A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension))
    (W : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hW : W.IsContinuous),
    (∀ w ∈ CommonClosureWeilDeligne.inertia F (base F), W.representation w = 1) →
    ∀ (Φ : CommonClosureWeilDeligne.GeometricFrobenius F (base F)) (m : ℤ),
      (m : ℚ) = P.artinConductor hsurj + (additiveConductor F ψ : ℚ) * A.rank →
    ∀ s : ℂ,
      (conditionalDeligneValue F e ε hε (base F) ψ μ
          (ExactGrothendieckGroup.continuousTensorSame (baseClass F A hA)
            (baseClass F W hW)) s : ℂ) =
        (conditionalDeligneValue F e ε hε (base F) ψ μ (baseClass F A hA) s : ℂ) ^ W.rank *
          LinearMap.det (W.representation Φ.val) ^ m

/-- Tate (4.1.6), with Tate's (3.4.5) for general `ψ`: a continuous Weil–Deligne
representation has spectral exponent `a(ρ) + dim V^I - dim V_N^I + n(ψ) dim V`. -/
def WeilDeligneSpectralConductorStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (A : CommonClosureWeilDeligne.Pair.{uF, uV} F (base F))
    (hA : A.toFiniteRepresentation.IsContinuous)
    (P : Presentation.{uF, uV} F A.toFiniteRepresentation)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension))
    (Φ : CommonClosureWeilDeligne.GeometricFrobenius F (base F)) (s : ℂ),
    (CommonClosureWeilDeligne.conditionalEpsilonValue F e ε hε (base F) ψ μ A hA Φ s : ℂ) =
      (CommonClosureWeilDeligne.conditionalEpsilonValue F e ε hε (base F) ψ μ A hA Φ 0 : ℂ) *
        (baseCardinality F : ℂ) ^
          (-(((P.artinConductor hsurj : ℚ) : ℂ) +
              (WeilDeligne.conductorCorrection A
                (CommonClosureWeilDeligne.inertia F (base F)) : ℂ) +
              (additiveConductor F ψ : ℂ) * (A.rank : ℂ)) * s)

end Langlands.LocalFactor.ConductorExponent

namespace Langlands.LocalFactor

/-- Tate (3.4.5), (3.4.6), (4.1.6) and Deligne (5.5.1)–(5.5.3), for every p-adic
field and every supplied local-constant system on its common closure. -/
def ConductorExponentStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    ConductorExponent.SpectralConductorStatement.{uF, uV} F ∧
      ConductorExponent.UnramifiedCharacterStatement.{uF, uV} F ∧
      ConductorExponent.UnramifiedTensorStatement.{uF, uV} F ∧
      ConductorExponent.WeilDeligneSpectralConductorStatement.{uF, uV} F

end Langlands.LocalFactor
