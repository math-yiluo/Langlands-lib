import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Langlands.Representation.Category.Twist
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Discrete-series classes and actual unramified twist orbits

The representation objects and their classes are the canonical smooth ones.
The quotient subgroup and positive norm characters remain explicit until their
rational-point specialization. Finiteness, torus structures and orbit measures
are separate obligations.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]

section Classes

variable [IsTopologicalGroup G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]

/-- Square-integrability on the prescribed quotient, descended to the canonical
smooth dual by its proved invariance under actual representation equivalence. -/
def IsDiscreteSeriesClass :
    SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) → Prop :=
  Quotient.lift
    (fun π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G) =>
      IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ)
    (by
      intro π σ h
      obtain ⟨e⟩ := h
      exact propext
        (isSquareIntegrableModCentralSubgroup_iff_of_equiv A hA
          (SmoothRep.equivOfIso
            ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e)) μ))

@[simp]
theorem isDiscreteSeriesClass_mk
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    IsDiscreteSeriesClass A hA μ (Quotient.mk _ π) ↔
      IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ :=
  Iff.rfl

/-- The source's `E₂(G)` after specializing `A` to the actual split center.
Its elements are actual irreducible admissible isomorphism classes. -/
abbrev DiscreteSeriesClass :=
  {ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) |
    IsDiscreteSeriesClass A hA μ ω}

/-- Send an actual discrete-series smooth object to its canonical class. -/
def discreteSeriesClass
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ) :
    DiscreteSeriesClass A hA μ :=
  ⟨Quotient.mk _ π, hπ⟩

theorem isDiscreteSeriesClass_unitaryTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    (hω : IsDiscreteSeriesClass A hA μ ω) :
    IsDiscreteSeriesClass A hA μ (SmoothDualClass.twist χ hχ ω) := by
  induction ω using Quotient.inductionOn with
  | h π =>
    exact isSquareIntegrableModCentralSubgroup_unitaryTwist A hA χ hχ hu μ hω

end Classes

section Actions

variable [NonarchimedeanGroup G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
variable {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- The actual character twist action on the entire canonical smooth dual. -/
instance unramifiedTwistAction :
    MulAction (unramifiedCharacters ν)
      (SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) where
  smul χ ω :=
    SmoothDualClass.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) ω
  one_smul ω := SmoothDualClass.twist_one _ ω
  mul_smul χ η ω :=
    (SmoothDualClass.twist_twist χ.val.toMonoidHom η.val.toMonoidHom _ _ _ ω).symm

/-- The subgroup of all unramified characters fixing the underlying class.
Its finiteness and containment in the unitary subgroup are not asserted here. -/
def unramifiedTwistStabilizer
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)) :
    Subgroup (unramifiedCharacters ν) :=
  MulAction.stabilizer (unramifiedCharacters ν) ω

/-- Unitary unramified twisting preserves the actual square-integrability
condition and hence acts on the discrete-series subtype. -/
instance unitaryUnramifiedTwistAction :
    MulAction (unitaryUnramifiedCharacters ν) (DiscreteSeriesClass A hA μ) where
  smul χ ω :=
    ⟨SmoothDualClass.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν ⟨χ.val, χ.property.1⟩) ω.val,
      isDiscreteSeriesClass_unitaryTwist A hA μ χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν ⟨χ.val, χ.property.1⟩) χ.property.2
        ω.val ω.property⟩
  one_smul ω := by
    apply Subtype.ext
    exact SmoothDualClass.twist_one _ ω.val
  mul_smul χ η ω := by
    apply Subtype.ext
    exact
      (SmoothDualClass.twist_twist χ.val.toMonoidHom η.val.toMonoidHom _ _ _ ω.val).symm

@[simp]
theorem unitaryUnramified_smul_val
    (χ : unitaryUnramifiedCharacters ν) (ω : DiscreteSeriesClass A hA μ) :
    (χ • ω).val =
      SmoothDualClass.twist χ.val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν ⟨χ.val, χ.property.1⟩) ω.val :=
  rfl

/-- The actual subset consisting of the unitary unramified twists of a class. -/
def discreteSeriesOrbit (ω : DiscreteSeriesClass A hA μ) :
    Set (DiscreteSeriesClass A hA μ) :=
  MulAction.orbit (unitaryUnramifiedCharacters ν) ω

/-- The actual unitary unramified stabilizer of a discrete-series class. -/
def discreteSeriesStabilizer (ω : DiscreteSeriesClass A hA μ) :
    Subgroup (unitaryUnramifiedCharacters ν) :=
  MulAction.stabilizer (unitaryUnramifiedCharacters ν) ω

/-- All unitary unramified twist orbits, as the actual orbit quotient. -/
abbrev DiscreteSeriesOrbitClass :=
  MulAction.orbitRel.Quotient (unitaryUnramifiedCharacters ν)
    (DiscreteSeriesClass A hA μ)

/-- The orbit-stabilizer parameterization uses actual character twisting. -/
def discreteSeriesOrbitEquiv (ω : DiscreteSeriesClass A hA μ) :
    ((unitaryUnramifiedCharacters ν) ⧸ discreteSeriesStabilizer A hA μ ν ω) ≃
      discreteSeriesOrbit A hA μ ν ω :=
  (MulAction.orbitEquivQuotientStabilizer (unitaryUnramifiedCharacters ν) ω).symm

@[simp]
theorem discreteSeriesOrbitEquiv_mk
    (ω : DiscreteSeriesClass A hA μ) (χ : unitaryUnramifiedCharacters ν) :
    (discreteSeriesOrbitEquiv A hA μ ν ω (QuotientGroup.mk χ)).val = χ • ω :=
  rfl

theorem mem_discreteSeriesOrbit_iff
    (ω η : DiscreteSeriesClass A hA μ) :
    η ∈ discreteSeriesOrbit A hA μ ν ω ↔
      ∃ χ : unitaryUnramifiedCharacters ν, χ • ω = η :=
  Iff.rfl

theorem mem_discreteSeriesStabilizer_iff
    (ω : DiscreteSeriesClass A hA μ) (χ : unitaryUnramifiedCharacters ν) :
    χ ∈ discreteSeriesStabilizer A hA μ ν ω ↔ χ • ω = ω :=
  Iff.rfl

end Actions

end Langlands.Plancherel
