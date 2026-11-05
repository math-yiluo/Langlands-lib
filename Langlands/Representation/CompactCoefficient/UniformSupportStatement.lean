import Langlands.Representation.CompactCoefficient.Classes
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# One common compact support for fixed-level compact coefficients

This is the explicit uniformity needed in the coefficient-space argument of
Renard VI.3.4. The compact set is selected before every representation, vector
and invariant dual functional. Inversion matches the published inverse-
coefficient and left-Haar separation machinery.
-/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A single compact set contains all inverse coefficients of all compact
irreducible classes at the specified level. Invariance under an open subgroup
makes each tested algebraic-dual functional smooth; no finite-dimensionality
or admissibility assumption is present. -/
def HasUniformFixedLevelCoefficientSupport (K : Subgroup G) : Prop :=
  ∃ C : Set G, IsCompact C ∧
    ∀ (D : IrreducibleCompactCoefficientRep.{uG, uV} G)
      (v : D.obj), v ∈ fixedVectors D.obj.representation K →
      ∀ ℓ : Module.Dual ℂ D.obj,
        (∀ k ∈ K, ∀ w, ℓ (D.obj.representation k w) = ℓ w) →
        Function.support (fun g : G => ℓ (D.obj.representation g⁻¹ v)) ⊆ C

/-- The general coefficient-space reduction behind Renard VI.3.4: a common
compact support bounds the number of actual compact irreducible classes
having nonzero fixed vectors. The measure is only assumed left Haar. -/
def UniformSupportFixedLevelFinitenessStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G), IsCompact (K : Set G) →
    HasUniformFixedLevelCoefficientSupport.{uG, uV} K.toSubgroup →
    (fixedStratum.{uG, uV} K.toSubgroup).Finite

end Langlands.CompactCoefficientClass
