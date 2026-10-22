import Langlands.LocalFactor.NonabelianSystem
import Langlands.VirtualRepresentation.Weil.ExactRealization
import Langlands.VirtualRepresentation.Weil.Ramification
import Langlands.VirtualRepresentation.ExactTensor
import Langlands.VirtualRepresentation.ExactDeterminant

/-!
# Deligne--Henniart virtual twist stability

The actual local Weil lattice maps to the base component of the existing
common-closure system. All arithmetic assertions below are propositions.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local
open LocalWeil.Ramification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The base field as its actual image in the fixed algebraic closure. -/
def baseExtension : Extension F := ⟨⊥, inferInstance⟩

/-- Its fixing subgroup is the entire local Weil group. -/
theorem baseWeil_eq_top : weilSubgroup F (baseExtension F) = ⊤ := by
  change Subgroup.comap _ (⊥ : IntermediateField F.Carrier
    (AlgebraicClosure F.Carrier)).fixingSubgroup = ⊤
  rw [IntermediateField.fixingSubgroup_bot]
  exact Subgroup.comap_top _

/-- The literal inclusion into the base Weil group, with its inherited topology. -/
def baseWeilInclusion : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F where
  toMonoidHom := (weilSubgroup F (baseExtension F)).subtype
  continuous_toFun := continuous_subtype_val

/-- Forward realization, then restriction to the whole group written as a subgroup.
No inverse to the irreducible-lattice realization is selected. -/
def realizeAtBase :
    LocalWeil.Lattice.{uF, max uF uV} F →ₗ[ℤ]
      Virtual.{uF, uV} F (baseExtension F) :=
  (ExactGrothendieckGroup.continuousRestrict (baseWeilInclusion F)).comp
    (LocalWeil.realizeExact F)

/-- Dimension is unchanged by the literal base-component realization. -/
theorem degree_realizeAtBase (v : LocalWeil.Lattice.{uF, max uF uV} F) :
    degree F (baseExtension F) (realizeAtBase F v) = LocalWeil.degree F v := by
  unfold realizeAtBase
  rw [LinearMap.comp_apply, ExactGrothendieckGroup.degree_continuousRestrict,
    LocalWeil.degree_realizeExact]

/-- The finite signed expression for the Artin conductor on wild support.
The arithmetic assertion that this equals the usual Artin conductor is not
part of this constructor; its provenance is DH81 sections 0.5--0.6. -/
def wildArtinSum (v : LocalWeil.Lattice.{uF, max uF uV} F) : ℝ :=
  v.sum fun b n => (n : ℝ) * (b.1 : ℕ) * (1 + breakLabel F b)

/-- The exact twisting relation, tested on all dimension-zero virtual Weil
combinations below the strict half-break bound, and on every Haar measure.
Every lift of the specified field element has the same required value. -/
def ExactWitness (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (v : LocalWeil.Lattice.{uF, max uF uV} F) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F))
    (γ : (baseExtension F).fieldˣ) : Prop :=
  ∀ w : LocalWeil.Lattice.{uF, max uF uV} F,
    LocalWeil.degree F w = 0 →
    AllBreaksBelow F w (a / 2) →
    ∀ (μ : HaarMeasure F (baseExtension F))
      (g : weilSubgroup F (baseExtension F)),
      reciprocityUnits F e (baseExtension F) g = γ →
      ε (baseExtension F) ψ μ
          (ExactGrothendieckGroup.continuousTensorSame
            (realizeAtBase F w) (realizeAtBase F v)) =
        ExactGrothendieckGroup.determinantCharacter
          (ContinuousPredicate F (baseExtension F)) (realizeAtBase F w) g

/-- The coarser relation in DH81 4.2.1: the ratio is a root of unity of
power-of-p order. Its exponent may depend on the test representation. -/
def ApproximateWitness (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (v : LocalWeil.Lattice.{uF, max uF uV} F) (a : ℝ)
    (ψ : AdditiveCharacter F (baseExtension F))
    (γ : (baseExtension F).fieldˣ) : Prop :=
  ∀ w : LocalWeil.Lattice.{uF, max uF uV} F,
    LocalWeil.degree F w = 0 →
    AllBreaksBelow F w a →
    ∀ (μ : HaarMeasure F (baseExtension F))
      (g : weilSubgroup F (baseExtension F)),
      reciprocityUnits F e (baseExtension F) g = γ →
      ∃ n : ℕ,
        ε (baseExtension F) ψ μ
            (ExactGrothendieckGroup.continuousTensorSame
              (realizeAtBase F w) (realizeAtBase F v)) ^ (p ^ n) =
          ExactGrothendieckGroup.determinantCharacter
            (ContinuousPredicate F (baseExtension F)) (realizeAtBase F w) g ^ (p ^ n)

/-- DH81 4.6, including its full uniqueness coset, compatibility with 4.2,
and the valuation furnished by 4.2.2. Nonempty signed constituent support
is explicit; the zero test representation is allowed without defining beta(0). -/
def VirtualStabilityStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F),
    IsSystem F e ε →
    ∀ (ψ : AdditiveCharacter F (baseExtension F))
      (v : LocalWeil.Lattice.{uF, max uF uV} F)
      (hv : (breakSupport F v).Nonempty),
      PositiveBreakSupport F v →
      let a := minimumBreak F v hv
      ∃ γ : (baseExtension F).fieldˣ,
        ((fieldData F (baseExtension F)).ord (γ : (baseExtension F).field) : ℝ) =
          wildArtinSum F v + (LocalWeil.degree F v : ℝ) *
            (fieldData F (baseExtension F)).additiveConductor ψ ∧
        ExactWitness F e ε v a ψ γ ∧
        (∀ γ' : (baseExtension F).fieldˣ,
          ExactWitness F e ε v a ψ γ' ↔
            γ' * γ⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits ⌈a / 2⌉₊) ∧
        ∃ γ₀ : (baseExtension F).fieldˣ,
          ApproximateWitness F e ε v a ψ γ₀ ∧
          γ * γ₀⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits 1 ∧
          ∀ γ₀' : (baseExtension F).fieldˣ,
            ApproximateWitness F e ε v a ψ γ₀' ↔
              γ₀' * γ₀⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits 1

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
