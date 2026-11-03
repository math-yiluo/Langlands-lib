import Langlands.Representation.Plancherel.DiscreteSeriesOrbits
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Central restriction and actual unramified twist stabilizers -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {I : Type uI} (ν : I → (G →* ℝ≥0ˣ)) (A : Subgroup G)

/-- Restriction of the actual unramified characters to a specified subgroup. -/
def unramifiedCharacterRestriction : unramifiedCharacters ν →* (A →* ℂˣ) where
  toFun χ := χ.val.toMonoidHom.comp A.subtype
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem unramifiedCharacterRestriction_apply
    (χ : unramifiedCharacters ν) (a : A) :
    unramifiedCharacterRestriction ν A χ a = χ.val a := rfl

/-- The restriction kernel, as a subgroup of the actual character group. -/
def centralTrivialUnramifiedCharacters : Subgroup (unramifiedCharacters ν) :=
  (unramifiedCharacterRestriction ν A).ker

theorem mem_centralTrivialUnramifiedCharacters
    (χ : unramifiedCharacters ν) :
    χ ∈ centralTrivialUnramifiedCharacters ν A ↔ ∀ a : A, χ.val a = 1 := by
  change unramifiedCharacterRestriction ν A χ = 1 ↔ _
  exact ⟨fun h a => DFunLike.congr_fun h a,
    fun h => MonoidHom.ext h⟩

section NormalSubgroup

variable [A.Normal]

/-- A character trivial on the common norm kernel and on `A` descends to
their actual quotient. The quotient character is algebraic here. -/
def centralTrivialUnramifiedCharacterDescend
    (χ : centralTrivialUnramifiedCharacters ν A) :
    G ⧸ (commonNormKernel ν ⊔ A) →* ℂˣ :=
  QuotientGroup.lift (commonNormKernel ν ⊔ A) χ.val.val.toMonoidHom
    (sup_le χ.val.property (by
      intro a ha
      exact (mem_centralTrivialUnramifiedCharacters ν A χ.val).mp χ.property ⟨a, ha⟩))

@[simp]
theorem centralTrivialUnramifiedCharacterDescend_mk
    (χ : centralTrivialUnramifiedCharacters ν A) (g : G) :
    centralTrivialUnramifiedCharacterDescend ν A χ (QuotientGroup.mk g) =
      χ.val.val g := rfl

theorem centralTrivialUnramifiedCharacterDescend_injective :
    Function.Injective (centralTrivialUnramifiedCharacterDescend ν A) := by
  intro χ η h
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro g
  exact DFunLike.congr_fun h (QuotientGroup.mk g)

/-- Finiteness of the displayed group quotient implies finiteness of the
restriction kernel, without any representation-theoretic assumption. -/
theorem finite_centralTrivialUnramifiedCharacters
    [Finite (G ⧸ (commonNormKernel ν ⊔ A))] :
    Finite (centralTrivialUnramifiedCharacters ν A) :=
  Finite.of_injective _ (centralTrivialUnramifiedCharacterDescend_injective ν A)

/-- Every character in this restriction kernel is unitary when the quotient
is finite. -/
theorem centralTrivialUnramifiedCharacter_norm_eq_one
    [Finite (G ⧸ (commonNormKernel ν ⊔ A))]
    (χ : centralTrivialUnramifiedCharacters ν A) (g : G) :
    ‖(χ.val.val g : ℂ)‖ = 1 := by
  let f := (Units.coeHom ℂ).comp
    (centralTrivialUnramifiedCharacterDescend ν A χ)
  exact (f.isOfFinOrder (isOfFinOrder_of_finite (QuotientGroup.mk g))).norm_eq_one

end NormalSubgroup

section TopologicalGroup

variable [IsTopologicalGroup G]

/-- Equality of actual canonical smooth-dual classes after twisting forces
triviality on every central element. -/
theorem smoothDualClass_twist_eq_self_on_center
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (h : SmoothDualClass.twist χ hχ ω = ω) (z : Subgroup.center G) :
    χ z = 1 := by
  induction ω using Quotient.inductionOn with
  | h π =>
    obtain ⟨e⟩ := Quotient.exact h
    exact Classification.IntegralTwistFreeness.character_eq_one_on_center
      π.obj.representation π.property.2 π.property.1 χ
      (SmoothRep.equivOfIso
        ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e.symm)) z

end TopologicalGroup

variable [NonarchimedeanGroup G]

/-- The full unramified stabilizer is contained in the restriction kernel
for every central subgroup `A`. -/
theorem unramifiedTwistStabilizer_le_centralTrivial
    (hA : A ≤ Subgroup.center G)
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    unramifiedTwistStabilizer ν ω ≤ centralTrivialUnramifiedCharacters ν A := by
  intro χ hχ
  apply (mem_centralTrivialUnramifiedCharacters ν A χ).mpr
  intro a
  exact smoothDualClass_twist_eq_self_on_center ω χ.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker ν χ) hχ ⟨a, hA a.property⟩

variable [A.Normal]

/-- The actual stabilizer embeds into the dual of the actual central quotient. -/
def unramifiedTwistStabilizerEmbedding
    (hA : A ≤ Subgroup.center G)
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    unramifiedTwistStabilizer ν ω ↪
      (G ⧸ (commonNormKernel ν ⊔ A) →* ℂˣ) where
  toFun χ := centralTrivialUnramifiedCharacterDescend ν A
    ⟨χ.val, unramifiedTwistStabilizer_le_centralTrivial ν A hA ω χ.property⟩
  inj' := by
    intro χ η h
    have he := centralTrivialUnramifiedCharacterDescend_injective ν A h
    exact Subtype.ext
      (congrArg (fun x : centralTrivialUnramifiedCharacters ν A => x.val) he)

/-- The source's full stabilizer is finite under the explicit finite-quotient
structural premise. -/
theorem finite_unramifiedTwistStabilizer
    [Finite (G ⧸ (commonNormKernel ν ⊔ A))]
    (hA : A ≤ Subgroup.center G)
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    Finite (unramifiedTwistStabilizer ν ω) :=
  Finite.of_injective _ (unramifiedTwistStabilizerEmbedding ν A hA ω).injective

/-- A full unramified stabilizer character is already unitary under the same
structural premise. -/
theorem unramifiedTwistStabilizer_norm_eq_one
    [Finite (G ⧸ (commonNormKernel ν ⊔ A))]
    (hA : A ≤ Subgroup.center G)
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    (χ : unramifiedTwistStabilizer ν ω) (g : G) :
    ‖(χ.val.val g : ℂ)‖ = 1 :=
  centralTrivialUnramifiedCharacter_norm_eq_one ν A
    ⟨χ.val, unramifiedTwistStabilizer_le_centralTrivial ν A hA ω χ.property⟩ g

section DiscreteSeries

variable (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
variable [Finite (G ⧸ (commonNormKernel ν ⊔ A))]

/-- Under the finite-quotient premise, the unitary stabilizer used in the
actual orbit quotient is exactly the source's full unramified stabilizer. -/
def discreteSeriesStabilizerEquivFull
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesStabilizer A hA μ ν ω ≃*
      unramifiedTwistStabilizer ν ω.val where
  toFun χ := ⟨⟨χ.val.val, χ.val.property.1⟩, by
    exact congrArg (fun x : DiscreteSeriesClass A hA μ => x.val) χ.property⟩
  invFun χ := ⟨⟨χ.val.val, χ.val.property,
      unramifiedTwistStabilizer_norm_eq_one ν A hA ω.val χ⟩, by
    apply Subtype.ext
    exact χ.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

@[simp]
theorem discreteSeriesStabilizerEquivFull_apply
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ)
    (χ : discreteSeriesStabilizer A hA μ ν ω) (g : G) :
    (discreteSeriesStabilizerEquivFull ν A hA μ ω χ).val.val g =
      χ.val.val g := rfl

/-- The actual unitary stabilizer is finite; the proof does not assume
finiteness of any family of representations or twist orbits. -/
theorem finite_discreteSeriesStabilizer
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    Finite (discreteSeriesStabilizer A hA μ ν ω) := by
  let := finite_unramifiedTwistStabilizer ν A hA ω.val
  exact Finite.of_injective _ (discreteSeriesStabilizerEquivFull ν A hA μ ω).injective

end DiscreteSeries

end Langlands.Plancherel
