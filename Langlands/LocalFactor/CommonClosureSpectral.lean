import Langlands.LocalFactor.NonabelianSystem
import Langlands.LocalFactor.SpectralTwist
import Langlands.LocalField.Topology
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Spectral values of a supplied common-closure local-constant system

Actual degree characters twist the continuous exact virtual group. Deligne's
measure-dependent convention and Langlands' half-shifted self-dual convention
remain distinct. Neither a system nor a self-dual measure is chosen.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosureSpectral

open CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual base-field degree restricted to the fixing subgroup. It is not
renormalized to degree one at an extension-field geometric Frobenius. -/
def baseDegree (E : Extension F) : weilSubgroup F E →ₜ* Weil.Degree where
  toMonoidHom := (localDegree F).toMonoidHom.comp (weilSubgroup F E).subtype
  continuous_toFun := (localDegree F).continuous.comp continuous_subtype_val

/-- The actual cardinality of the residue field of the base field. -/
def baseCardinality : ℝ := F.canonicalTopologicalData.residueCardinality

theorem baseCardinality_pos : 0 < baseCardinality F := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change (0 : ℝ) < (Nat.card (IsLocalRing.ResidueField
    (ValuativeRel.valuation F.Carrier).integer) : ℝ)
  exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField
    (ValuativeRel.valuation F.Carrier).integer))

/-- The actual spectral norm power, using base cardinality and base degree. -/
def character (E : Extension F) (s : ℂ) : weilSubgroup F E →ₜ* ℂˣ :=
  SpectralTwist.character (baseDegree F E) (baseCardinality F) (baseCardinality_pos F) s

theorem character_apply (E : Extension F) (s : ℂ) (w : weilSubgroup F E) :
    (character F E s w : ℂ) =
      Complex.exp (-s * (Real.log (baseCardinality F) : ℂ)) ^
        (localDegree F w.val).toAdd :=
  SpectralTwist.character_apply _ _ _ _ _

/-- Spectral twisting of the actual continuous exact virtual group. -/
def virtualTwist (E : Extension F) (s : ℂ) :
    Virtual.{uF, uV} F E ≃ₗ[ℤ] Virtual.{uF, uV} F E :=
  SpectralTwist.virtual (baseDegree F E) (baseCardinality F) (baseCardinality_pos F) s

@[simp]
theorem virtualTwist_zero (E : Extension F) (x : Virtual.{uF, uV} F E) :
    virtualTwist F E 0 x = x :=
  LinearMap.congr_fun (SpectralTwist.virtual_zero
    (baseDegree F E) (baseCardinality F) (baseCardinality_pos F)) x

theorem virtualTwist_add (E : Extension F) (s t : ℂ) (x : Virtual.{uF, uV} F E) :
    virtualTwist F E s (virtualTwist F E t x) = virtualTwist F E (s + t) x :=
  LinearMap.congr_fun (SpectralTwist.virtual_add
    (baseDegree F E) (baseCardinality F) (baseCardinality_pos F) s t) x

theorem degree_virtualTwist (E : Extension F) (s : ℂ) (x : Virtual.{uF, uV} F E) :
    degree F E (virtualTwist F E s x) = degree F E x :=
  SpectralTwist.virtual_preserves_degree _ _ _ _ _

/-- Deligne's spectral value for an explicitly supplied, validated system.
The system proof is a hypothesis, not a theorem constructed here. -/
def conditionalDeligneValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (_hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x : Virtual.{uF, uV} F E) (s : ℂ) : ℂˣ :=
  ε E ψ μ (virtualTwist F E s x)

@[simp]
theorem conditionalDeligneValue_zero (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x : Virtual.{uF, uV} F E) :
    conditionalDeligneValue F e ε hε E ψ μ x 0 = ε E ψ μ x := by
  simp [conditionalDeligneValue]

/-- The existing intrinsic Fourier self-duality condition, on the canonical
intermediate-field topology and Borel space. -/
def IsSelfDual (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) : Prop :=
  letI := (fieldData F E).topology
  letI := (fieldData F E).valuativeRel
  letI := (fieldData F E).localField
  letI := (fieldData F E).fieldT2
  letI : NonarchimedeanRing E.field := by
    convert! ValuativeRel.nonarchimedeanRing E.field
    exact (ValuativeRel.valuation E.field).toTopologicalSpace_eq
  letI : MeasurableSpace E.field := borel E.field
  letI : BorelSpace E.field := ⟨rfl⟩
  HarmonicAnalysis.IsSelfDual ψ μ

/-- A supplied measure together with the existing self-duality property.
No inhabitant or existence assertion is provided. -/
abbrev SelfDualMeasure (E : Extension F) (ψ : AdditiveCharacter F E) :=
  {μ : HaarMeasure F E // IsSelfDual F E ψ μ}

/-- Langlands' constant: Deligne at the positive half twist, using a supplied
intrinsically self-dual measure. -/
def conditionalLanglandsConstant (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ)
    (x : Virtual.{uF, uV} F E) : ℂˣ :=
  conditionalDeligneValue F e ε hε E ψ μ.val x (1 / 2)

/-- The centered spectral convention applies a shift of `s - 1/2` before
Langlands' constant. -/
def conditionalLanglandsValue (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ)
    (x : Virtual.{uF, uV} F E) (s : ℂ) : ℂˣ :=
  conditionalLanglandsConstant F e ε hε E ψ μ (virtualTwist F E (s - 1 / 2) x)

/-- The two shifts add to `s`; the equality uses the constructed exact-twist
composition, without a local functional equation or a measure-existence theorem. -/
theorem conditionalLanglandsValue_eq (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : SelfDualMeasure F E ψ)
    (x : Virtual.{uF, uV} F E) (s : ℂ) :
    conditionalLanglandsValue F e ε hε E ψ μ x s =
      conditionalDeligneValue F e ε hε E ψ μ.val x s := by
  unfold conditionalLanglandsValue conditionalLanglandsConstant conditionalDeligneValue
  have hs : (1 / 2 : ℂ) + (s - 1 / 2) = s := by ring
  rw [virtualTwist_add, hs]

end Langlands.LocalFactor.CommonClosureSpectral
