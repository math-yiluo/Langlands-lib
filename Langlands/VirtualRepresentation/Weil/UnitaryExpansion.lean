import Langlands.VirtualRepresentation.Weil.UnitaryExactExpansionProof

/-!
# Canonical effective unitary expansions

Project the published exact Jordan–Hölder coefficients to the genuine unitary
basis. The effective expansion theorem proves that this projection recovers the
whole exact class of an actual continuous unitary representation.
-/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- Extract the unitary irreducible coefficients of an arbitrary exact virtual
class. Recovery of the entire class is asserted below for unitary objects. -/
def unitaryExactCoefficients :
    ContinuousExactGroup.{uG, uV} G →ₗ[ℤ] UnitaryLattice.{uG, uV} G :=
  (restrictUnitary G).comp (exactCoefficients G)

@[simp]
theorem restrictUnitary_includeUnitary (x : UnitaryLattice.{uG, uV} G) :
    restrictUnitary G (includeUnitary G x) = x :=
  Finsupp.comapDomain_mapDomain Subtype.val Subtype.val_injective x

@[simp]
theorem unitaryExactCoefficients_realizeExact_includeUnitary
    (x : UnitaryLattice.{uG, uV} G) :
    unitaryExactCoefficients G (realizeExact G (includeUnitary G x)) = x := by
  simp only [unitaryExactCoefficients, LinearMap.comp_apply,
    exactCoefficients_realizeExact, restrictUnitary_includeUnitary]

/-- Inclusion of the unitary basis retains every coefficient. -/
theorem includeUnitary_injective : Function.Injective (includeUnitary.{uG, uV} G) :=
  Function.LeftInverse.injective (restrictUnitary_includeUnitary G)

/-- The full exact class determines its unitary-lattice expansion uniquely. -/
theorem realizeExact_includeUnitary_injective :
    Function.Injective (fun x : UnitaryLattice.{uG, uV} G =>
      realizeExact G (includeUnitary G x)) :=
  Function.LeftInverse.injective (unitaryExactCoefficients_realizeExact_includeUnitary G)

/-- Any supplied full expansion agrees with the canonical unitary coefficients.
No positivity premise on the supplied expansion is needed. -/
theorem unitaryExactCoefficients_eq_of_expansion
    {a : ContinuousExactGroup.{uG, uV} G} {x : UnitaryLattice.{uG, uV} G}
    (h : ExactExpansion G a (includeUnitary G x)) :
    unitaryExactCoefficients G a = x := by
  rw [← h]
  exact unitaryExactCoefficients_realizeExact_includeUnitary G x

variable {G}

/-- For an actual continuous unitary object the extracted coefficients are
nonnegative. Existence comes from the proved effective expansion theorem. -/
theorem unitaryExactCoefficients_ofRepresentation_mem_effective
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous) (hu : A.IsUnitary) :
    unitaryExactCoefficients G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩) ∈
      effective := by
  obtain ⟨x, hx, he⟩ := effectiveUnitaryExactExpansion G A hc hu
  rw [unitaryExactCoefficients_eq_of_expansion G he]
  exact hx

/-- An actual continuous unitary representation gives a canonical element of
the nonnegative unitary lattice, without a supplied irreducible expansion. -/
def effectiveUnitaryExpansion
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous) (hu : A.IsUnitary) :
    (effective : AddSubmonoid (UnitaryLattice.{uG, uV} G)) :=
  ⟨unitaryExactCoefficients G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩),
    unitaryExactCoefficients_ofRepresentation_mem_effective A hc hu⟩

/-- The constructed effective element expands the entire original exact class. -/
theorem effectiveUnitaryExpansion_spec
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous) (hu : A.IsUnitary) :
    ExactExpansion G (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩)
      (includeUnitary G (effectiveUnitaryExpansion A hc hu).val) := by
  obtain ⟨x, hx, he⟩ := effectiveUnitaryExactExpansion G A hc hu
  change ExactExpansion G _ (includeUnitary G (unitaryExactCoefficients G _))
  rw [unitaryExactCoefficients_eq_of_expansion G he]
  exact he

/-- Its integral degree is the dimension of the full original carrier. -/
@[simp]
theorem effectiveUnitaryExpansion_degree
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hc : A.IsContinuous) (hu : A.IsUnitary) :
    unitaryDegree G (effectiveUnitaryExpansion A hc hu).val = (A.rank : ℤ) := by
  calc
    _ = ExactGrothendieckGroup.degree _
        (realizeExact G (includeUnitary G (effectiveUnitaryExpansion A hc hu).val)) :=
      (degree_realizeExact G _).symm
    _ = ExactGrothendieckGroup.degree _
        (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩) :=
      congrArg _ (effectiveUnitaryExpansion_spec A hc hu)
    _ = _ := ExactGrothendieckGroup.degree_ofRepresentation _ _

/-- Actual invertible intertwiners preserve the canonical effective element. -/
theorem effectiveUnitaryExpansion_eq_of_equiv
    {A B : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hcA : A.IsContinuous) (huA : A.IsUnitary)
    (hcB : B.IsContinuous) (huB : B.IsUnitary) (e : FiniteRepresentation.Equiv A B) :
    effectiveUnitaryExpansion A hcA huA = effectiveUnitaryExpansion B hcB huB := by
  apply Subtype.ext
  exact congrArg (unitaryExactCoefficients G)
    (ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ e)

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uF uW

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Canonical unitary coefficient extraction on the actual local exact group. -/
abbrev unitaryExactCoefficients :
    ContinuousExactGroup.{uF, uW} F →ₗ[ℤ] UnitaryLattice.{uF, uW} F :=
  Weil.unitaryExactCoefficients (localWeilGroup F)

variable {F}

/-- Canonical effective expansion for every actual local continuous unitary
representation, retaining its independent carrier universe. -/
abbrev effectiveUnitaryExpansion
    (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F))
    (hc : A.IsContinuous) (hu : A.IsUnitary) :
    (VirtualRepresentation.effective : AddSubmonoid (UnitaryLattice.{uF, uW} F)) :=
  Weil.effectiveUnitaryExpansion A hc hu

/-- The actual local construction recovers the full exact class. -/
theorem effectiveUnitaryExpansion_spec
    (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F))
    (hc : A.IsContinuous) (hu : A.IsUnitary) :
    ExactExpansion F (ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩)
      (includeUnitary F (effectiveUnitaryExpansion A hc hu).val) :=
  Weil.effectiveUnitaryExpansion_spec A hc hu

@[simp]
theorem effectiveUnitaryExpansion_degree
    (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F))
    (hc : A.IsContinuous) (hu : A.IsUnitary) :
    unitaryDegree F (effectiveUnitaryExpansion A hc hu).val = (A.rank : ℤ) :=
  Weil.effectiveUnitaryExpansion_degree A hc hu

end Langlands.VirtualRepresentation.LocalWeil
