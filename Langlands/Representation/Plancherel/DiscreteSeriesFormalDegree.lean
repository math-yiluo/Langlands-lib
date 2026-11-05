import Langlands.Representation.Plancherel.FormalDegreeComparisons
import Langlands.Representation.Plancherel.DiscreteSeriesOrbits

/-!
# Formal degrees on the canonical discrete-series classes and twist orbits

The degree is the Schur normalization of an actual representative on the fixed
central quotient and measure. Equivalence invariance removes the representative
choice, and unitary twist invariance descends it to the existing orbit quotient.
-/

noncomputable section

open MeasureTheory CategoryTheory
open scoped NNReal

namespace Langlands.Plancherel

open Langlands.HarishChandraSchwartz

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

section Classes

variable [IsTopologicalGroup G]

/-- The actual Schur degree of a canonical discrete-series class. -/
def discreteSeriesFormalDegree (ω : DiscreteSeriesClass.{uG, uV} A hA μ) : ℝ :=
  let π := Quotient.out ω.val
  let hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ := by
    change IsDiscreteSeriesClass A hA μ (Quotient.mk _ π)
    exact Eq.mpr
      (congrArg (IsDiscreteSeriesClass A hA μ) (Quotient.out_eq ω.val)) ω.property
  representationFormalDegree A hA μ hcof hπ π.property.1

/-- Computation on every actual representative proves independence of its
choice in the canonical class quotient. -/
@[simp]
theorem discreteSeriesFormalDegree_mk
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ) :
    discreteSeriesFormalDegree A hA μ hcof (discreteSeriesClass A hA μ π hπ) =
      representationFormalDegree A hA μ hcof hπ π.property.1 := by
  let q : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) := Quotient.mk _ π
  have he : Nonempty ((Quotient.out q) ≅ π) := Quotient.exact (Quotient.out_eq q)
  obtain ⟨e⟩ := he
  let eρ := SmoothRep.equivOfIso
    ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e)
  exact (representationFormalDegree_equiv A hA μ hcof
    eρ ((isSquareIntegrableModCentralSubgroup_iff_of_equiv A hA eρ μ).mpr hπ)
    (Quotient.out q).property.1 hπ π.property.1).symm

theorem discreteSeriesFormalDegree_pos (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    0 < discreteSeriesFormalDegree A hA μ hcof ω := by
  unfold discreteSeriesFormalDegree
  exact representationFormalDegree_pos _ _ _ _ _ _

/-- The descended degree retains the original Schur normalization for every
scalar-action witness of an actual representative. -/
theorem discreteSeriesFormalDegree_eq_formalDegree
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ)
    {η : A →* ℂˣ}
    (hη : ∀ (a : A) (v : π.obj), π.obj.representation a v = (η a : ℂ) • v) :
    discreteSeriesFormalDegree A hA μ hcof (discreteSeriesClass A hA μ π hπ) =
      formalDegree A hA μ hη hcof hπ π.property.1 := by
  rw [discreteSeriesFormalDegree_mk]
  exact representationFormalDegree_eq_formalDegree A hA μ hcof hη hπ π.property.1

/-- All smooth norm-one character twists preserve the class degree. -/
theorem discreteSeriesFormalDegree_unitaryTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesFormalDegree A hA μ hcof
      ⟨SmoothDualClass.twist χ hχ ω.val,
        isDiscreteSeriesClass_unitaryTwist A hA μ χ hχ hu ω.val ω.property⟩ =
      discreteSeriesFormalDegree A hA μ hcof ω := by
  rcases ω with ⟨ω, hω⟩
  induction ω using Quotient.inductionOn with
  | h π =>
    change discreteSeriesFormalDegree A hA μ hcof
      (discreteSeriesClass A hA μ (IrreducibleAdmissibleRep.twist χ hχ π)
        (isSquareIntegrableModCentralSubgroup_unitaryTwist A hA χ hχ hu μ hω)) =
      discreteSeriesFormalDegree A hA μ hcof (discreteSeriesClass A hA μ π hω)
    exact
      (discreteSeriesFormalDegree_mk A hA μ hcof
        (IrreducibleAdmissibleRep.twist χ hχ π)
        (isSquareIntegrableModCentralSubgroup_unitaryTwist A hA χ hχ hu μ hω)).trans
      ((representationFormalDegree_unitaryTwist A hA μ hcof χ hχ hu hω π.property.1).trans
        (discreteSeriesFormalDegree_mk A hA μ hcof π hω).symm)

end Classes

section Orbits

variable [NonarchimedeanGroup G] {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- The existing unitary unramified action preserves the actual class degree. -/
@[simp]
theorem discreteSeriesFormalDegree_smul
    (χ : unitaryUnramifiedCharacters ν) (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesFormalDegree A hA μ hcof (χ • ω) =
      discreteSeriesFormalDegree A hA μ hcof ω :=
  discreteSeriesFormalDegree_unitaryTwist A hA μ hcof χ.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker ν ⟨χ.val, χ.property.1⟩) χ.property.2 ω

/-- The Schur degree on the existing quotient of unitary unramified twist
orbits, with the central quotient and its measure unchanged. -/
def discreteSeriesOrbitFormalDegree
    (O : DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μ ν) : ℝ :=
  Quotient.lift (discreteSeriesFormalDegree A hA μ hcof)
    (by
      intro ω η h
      obtain ⟨χ, rfl⟩ := h
      exact discreteSeriesFormalDegree_smul A hA μ hcof ν χ η) O

@[simp]
theorem discreteSeriesOrbitFormalDegree_mk
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesOrbitFormalDegree A hA μ hcof ν (Quotient.mk _ ω) =
      discreteSeriesFormalDegree A hA μ hcof ω :=
  rfl

theorem discreteSeriesOrbitFormalDegree_pos
    (O : DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μ ν) :
    0 < discreteSeriesOrbitFormalDegree A hA μ hcof ν O := by
  induction O using Quotient.inductionOn with
  | h ω => exact discreteSeriesFormalDegree_pos A hA μ hcof ω

/-- Every member of an orbit has the orbit's constructed formal degree. -/
theorem discreteSeriesOrbitFormalDegree_eq_of_mem
    (ω η : DiscreteSeriesClass.{uG, uV} A hA μ)
    (hη : η ∈ discreteSeriesOrbit A hA μ ν ω) :
    discreteSeriesOrbitFormalDegree A hA μ hcof ν (Quotient.mk _ ω) =
      discreteSeriesFormalDegree A hA μ hcof η := by
  obtain ⟨χ, rfl⟩ := hη
  exact (discreteSeriesFormalDegree_smul A hA μ hcof ν χ ω).symm

end Orbits

end Langlands.Plancherel
