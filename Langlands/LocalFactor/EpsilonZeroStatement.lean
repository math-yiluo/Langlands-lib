import Langlands.LocalFactor.ConductorExponentStatement
import Langlands.Weil.Representation.TwistProperties

/-!
# Deligne's modified local constant `ε₀`

Deligne (5.1) defines `ε₀(V, ψ, dx) = ε(V, ψ, dx) · det(-F | V^I)` for a
genuine continuous representation `V` of a nonarchimedean Weil group. Here it is
evaluated from a supplied local-constant system on the common closure, with the
actual inertia invariants and an explicitly supplied geometric Frobenius.
The laws below are Deligne's (5.2)–(5.6) for `ε₀`. They are propositions; no
system, presentation or Frobenius is constructed.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.EpsilonZero

open CommonClosure CommonClosureSpectral Weil.Local
open VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual inertia invariants `V^I` of a representation of the Weil subgroup of `E`. -/
abbrev inertiaInvariants (E : Extension F)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)) :
    FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E) :=
  FiniteRepresentation.invariants (CommonClosureWeilDeligne.inertia F E) A

/-- `det(-q_E^(-s) Φ | V^I)`: the determinant of `-Φ` on the inertia invariants of
the twist `V ω_s`, on which `Φ` acts as `q_E^(-s) Φ`. -/
def invariantDeterminant (E : Extension F)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (Φ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ) : ℂ :=
  LinearMap.det
    ((Complex.exp (-s * (Real.log (CommonClosureWeilDeligne.residueCardinality F E) : ℂ))) •
      (-(inertiaInvariants.{uF, uV} F E A).representation Φ.val))

/-- The exact virtual class of a genuine continuous representation. -/
abbrev genuineClass (E : Extension F)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hA : A.IsContinuous) : Virtual.{uF, uV} F E :=
  ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) ⟨A, hA⟩

/-- Deligne (5.1) at `V ω_s`: `ε₀(V, ψ, dx, s) = ε(V, ψ, dx, s) · det(-q_E^(-s) Φ | V^I)`,
for a supplied system and a supplied geometric Frobenius `Φ` over `E`. -/
def value (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hA : A.IsContinuous) (Φ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ) : ℂ :=
  (conditionalDeligneValue F e ε hε E ψ μ (genuineClass.{uF, uV} F E A hA) s : ℂ) *
    invariantDeterminant.{uF, uV} F E A Φ s

/-- Inertia acts trivially on `V^I`, so the determinant does not depend on the lift. -/
theorem invariantDeterminant_eq_of_frobenius (E : Extension F)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (Φ Ψ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ) :
    invariantDeterminant.{uF, uV} F E A Ψ s = invariantDeterminant.{uF, uV} F E A Φ s := by
  have hi := CommonClosureWeilDeligne.frobenius_coset F E Φ Ψ
  have ht : (inertiaInvariants.{uF, uV} F E A).representation (Ψ.val * Φ.val⁻¹) = 1 :=
    Representation.isTrivial_def
      ((inertiaInvariants.{uF, uV} F E A).representation.comp
        (CommonClosureWeilDeligne.inertia F E).subtype) ⟨_, hi⟩
  have hm := congrArg
    (fun f : Module.End ℂ (inertiaInvariants.{uF, uV} F E A) =>
      f * (inertiaInvariants.{uF, uV} F E A).representation Φ.val) ht
  simp only [← map_mul, inv_mul_cancel_right, one_mul] at hm
  unfold invariantDeterminant
  rw [hm]

/-- Hence `ε₀` does not depend on the supplied Frobenius lift either. -/
theorem value_eq_of_frobenius (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hA : A.IsContinuous) (Φ Ψ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ) :
    value F e ε hε E ψ μ A hA Ψ s = value F e ε hε E ψ μ A hA Φ s := by
  rw [value, value, invariantDeterminant_eq_of_frobenius]

/-- Deligne (5.2) for `ε₀`: multiplicativity on actual short exact sequences of
genuine continuous representations. -/
def AdditivityStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A B C : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E)}
    (hA : A.IsContinuous) (hB : B.IsContinuous) (hC : C.IsContinuous)
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation},
    FiniteRepresentation.IsShortExact f g →
    ∀ (Φ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ),
      value F e ε hε E ψ μ B hB Φ s =
        value F e ε hε E ψ μ A hA Φ s * value F e ε hε E ψ μ C hC Φ s

/-- Deligne (5.3) for `ε₀`: `ε₀(V, ψ, c dx) = c^(dim V) ε₀(V, ψ, dx)` for `c > 0`. -/
def HaarScalingStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (c : NNReal) (hc : 0 < c)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hA : A.IsContinuous) (Φ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ),
    value F e ε hε E ψ (scaleHaar F E μ c hc) A hA Φ s =
      (c : ℂ) ^ A.rank * value F e ε hε E ψ μ A hA Φ s

/-- Deligne (5.4) for `ε₀`, applied to `V ω_s`:
`ε₀(V, ψ(a·), dx, s) = det(V ω_s)(a) ‖a‖^(-dim V) ε₀(V, ψ, dx, s)`, where `a` is the
image of `w` under the supplied reciprocity, so `det(V ω_s)(a) = det V(w) ω_s(w)^(dim V)`. -/
def AdditiveCharacterScalingStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F),
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      ∀ (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
        (hA : A.IsContinuous) (Φ : CommonClosureWeilDeligne.GeometricFrobenius F E) (s : ℂ),
      value F e ε hε E (ψ.scale a) μ A hA Φ s =
        LinearMap.det (A.representation w) * (character F E s w : ℂ) ^ A.rank *
          ((fieldData F E).normalizedAbs (a : E.field) : ℂ) ^ (-(A.rank : ℤ)) *
          value F e ε hε E ψ μ A hA Φ s

open ConductorExponent in
/-- Deligne (5.5.2), second formula: `ε₀(V, s) = ε₀(V) q^(-(sw(V) + dim V (n(ψ) + 1)) s)`,
at the base field, with `sw(V)` the Swan conductor at any actual presentation. -/
def SpectralSwanStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) (P : Presentation.{uF, uV} F A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension))
    (Φ : CommonClosureWeilDeligne.GeometricFrobenius F (base F)) (s : ℂ),
    value F e ε hε (base F) ψ μ A hA Φ s =
      value F e ε hε (base F) ψ μ A hA Φ 0 *
        (baseCardinality F : ℂ) ^
          (-(((P.swanConductor hsurj : ℚ) : ℂ) +
              (A.rank : ℂ) * ((additiveConductor F ψ : ℂ) + 1)) * s)

open ConductorExponent in
/-- Deligne (5.5.1), second formula: for `χ` unramified and any `c` of valuation
`sw(V) + dim V (n(ψ) + 1)`, `ε₀(V χ, s) = χ(c) ε₀(V, s)`, at the base field. -/
def UnramifiedCharacterSwanStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (ψ : AdditiveCharacter F (base F)) (μ : HaarMeasure F (base F))
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F (base F)))
    (hA : A.IsContinuous) (P : Presentation.{uF, uV} F A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction F P.extension))
    (χ : FieldCharacter F (base F)),
    (∀ u : (base F).fieldˣ,
      (fieldData F (base F)).discreteValuation (u : (base F).field) = 1 → χ u = 1) →
    ∀ (m : ℤ),
      (m : ℚ) = P.swanConductor hsurj + (A.rank : ℚ) * ((additiveConductor F ψ : ℚ) + 1) →
    ∀ (c : (base F).fieldˣ),
      (fieldData F (base F)).discreteValuation (c : (base F).field) = WithZero.exp (-m) →
    ∀ (Φ : CommonClosureWeilDeligne.GeometricFrobenius F (base F)) (s : ℂ),
      value F e ε hε (base F) ψ μ
          (FiniteRepresentation.twist (weilCharacter F e (base F) χ).toMonoidHom A)
          (FiniteRepresentation.isContinuous_twist (weilCharacter F e (base F) χ) hA) Φ s =
        (χ c : ℂ) * value F e ε hε (base F) ψ μ A hA Φ s

open ConductorExponent in
/-- Deligne (5.5.3), second formula: for `W` unramified,
`ε₀(V ⊗ W) = det W(Φ)^(sw(V) + dim V (n(ψ) + 1)) ε₀(V)^(dim W)`, at the base field. -/
def UnramifiedTensorSwanStatement : Prop :=
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
      (m : ℚ) = P.swanConductor hsurj + (A.rank : ℚ) * ((additiveConductor F ψ : ℚ) + 1) →
    ∀ s : ℂ,
      value F e ε hε (base F) ψ μ (FiniteRepresentation.tensor A W)
          (FiniteRepresentation.isContinuous_tensor hA hW) Φ s =
        LinearMap.det (W.representation Φ.val) ^ m *
          value F e ε hε (base F) ψ μ A hA Φ s ^ W.rank

/-- Deligne (5.6.2) for `ε₀`, with the same `λ` as for `ε`: for nested finite
extensions `E ⊆ L` and a genuine continuous `V_L` of any dimension,
`ε₀_E(Ind V_L, ψ, μ_E) = λ^(dim V_L) ε₀_L(V_L, ψ ∘ Tr, μ_L)`, where
`λ = ε_E(Ind 1_L, ψ, μ_E) / ε_L(1_L, ψ ∘ Tr, μ_L)`. -/
def InductionStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε)
    (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (μL : HaarMeasure F L)
    (A : FiniteRepresentation.ContinuousObjects.{uF, max uF uV} (weilSubgroup F L))
    (ΦE : CommonClosureWeilDeligne.GeometricFrobenius F E)
    (ΦL : CommonClosureWeilDeligne.GeometricFrobenius F L) (s : ℂ),
    let ψL := traceCharacter F E L h ψ
    let one : Virtual.{uF, uV} F L :=
      ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)
    let lam := ε E ψ μ (induce F E L h one) * (ε L ψL μL one)⁻¹
    value F e ε hε E ψ μ (inducedRepresentation F E L h A).val
        (inducedRepresentation F E L h A).property ΦE s =
      (lam : ℂ) ^ A.val.rank * value F e ε hε L ψL μL A.val A.property ΦL s

end Langlands.LocalFactor.EpsilonZero

namespace Langlands.LocalFactor

/-- Deligne (5.2)–(5.6) for the modified constant `ε₀` of (5.1), for every p-adic
field and every supplied local-constant system on its common closure. -/
def EpsilonZeroStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    EpsilonZero.AdditivityStatement.{uF, uV} F ∧
      EpsilonZero.HaarScalingStatement.{uF, uV} F ∧
      EpsilonZero.AdditiveCharacterScalingStatement.{uF, uV} F ∧
      EpsilonZero.SpectralSwanStatement.{uF, uV} F ∧
      EpsilonZero.UnramifiedCharacterSwanStatement.{uF, uV} F ∧
      EpsilonZero.UnramifiedTensorSwanStatement.{uF, uV} F ∧
      EpsilonZero.InductionStatement.{uF, uV} F

end Langlands.LocalFactor
