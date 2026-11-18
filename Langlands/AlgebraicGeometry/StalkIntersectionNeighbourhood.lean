import Langlands.AlgebraicGeometry.StalkIntersectionAlgebra
import Langlands.AlgebraicGeometry.SemilocalStalkModel

/-! # Affine neighbourhoods from the localizations of the stalk intersection -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

/-- The algebraic localization property needed of the actual stalk
intersection. -/
def StalkIntersectionLocalizations (E : Set X) : Prop :=
  ∀ m : PrimeSpectrum (stalkIntersection X E), m.asIdeal.IsMaximal →
    ∃ x, ∃ hx : x ∈ E, letI := (stalkIntersectionToStalk E x hx).toAlgebra;
      IsLocalization.AtPrime (X.presheaf.stalk x) m.asIdeal

set_option backward.isDefEq.respectTransparency false in
/-- Canonical stalk maps and the localization property construct the affine
neighbourhood, leaving only the commutative-algebra property as an input. -/
def affineNeighbourhoodOfStalkIntersectionLocalizations
    [X.IsSeparated] {R : Type u} [CommRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation p]
    (E : Set X) (hE : E.Finite)
    [IsFractionRing (stalkIntersection X E) X.functionField]
    (hloc : StalkIntersectionLocalizations E) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  letI := stalkIntersectionAlgebra p E
  let M := affineStalkModelOfLocalizations p (stalkIntersection_generic_over p E) E
    (stalkIntersectionToStalk E)
    (stalkIntersectionToStalk_field_comp E) hloc
  exact affineNeighbourhoodOfAffineStalkModel p E hE M

/-- The empty or purely generic selected family has a common affine open
without any semilocal construction. -/
def affineNeighbourhoodOfSubsetGenericPoint
    (E : Set X) (hE : E ⊆ {genericPoint X}) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  apply Classical.choice
  obtain ⟨U, hU, hη, _⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top (genericPoint X))
  refine ⟨⟨U, hU, ?_⟩⟩
  intro x hx
  have hxη : x = genericPoint X := hE hx
  exact hxη ▸ hη

section Valuations

variable [IsLocallyNoetherian X]

/-- The family of actual valuation subrings for the selected normal points. -/
def normalStalkValuations (E : Set X)
    (hn : ∀ x ∈ E, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    E → ValuationSubring X.functionField :=
  fun x ↦ normalStalkValuationSubring X x (hn x x.property) (hd x x.property)

@[simp]
theorem normalStalkValuations_toSubring (E : Set X)
    (hn : ∀ x ∈ E, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) (x : E) :
    (normalStalkValuations E hn hd x).toSubring = stalkImageSubring X x := rfl

theorem normalStalkValuations_intersection (E : Set X)
    (hn : ∀ x ∈ E, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    (⨅ x : E, (normalStalkValuations E hn hd x).toSubring) =
      stalkIntersection X E := rfl

theorem normalStalkValuations_injective [X.IsSeparated] (E : Set X)
    (hn : ∀ x ∈ E, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    Function.Injective (normalStalkValuations E hn hd) := by
  intro x y h
  apply Subtype.ext
  apply stalkImageSubring_injective X
  exact congrArg ValuationSubring.toSubring h

theorem normalStalkValuations_isDiscreteValuationRing [X.IsSeparated] (E : Set X)
    (hn : ∀ x ∈ E, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (hη : ∀ x ∈ E, x ≠ genericPoint X) (x : E) :
    IsDiscreteValuationRing (normalStalkValuations E hn hd x) :=
  normalStalkValuationSubring_isDiscreteValuationRing X x
    (hn x x.property) (hd x x.property) (hη x x.property)

set_option backward.isDefEq.respectTransparency false in
/-- Transport a canonical valuation-subring localization back to the
original local ring. -/
theorem stalkIntersection_localization_of_valuation
    (E : Set X) (x : X) (hx : x ∈ E)
    (hn : IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (m : PrimeSpectrum (stalkIntersection X E))
    (hloc :
      letI : Algebra (stalkIntersection X E)
          (normalStalkValuationSubring X x hn hd) :=
        (Subring.inclusion
          (show stalkIntersection X E ≤
              (normalStalkValuationSubring X x hn hd).toSubring from
            iInf_le (fun y : E ↦ stalkImageSubring X y) ⟨x, hx⟩)).toAlgebra;
      IsLocalization.AtPrime (normalStalkValuationSubring X x hn hd) m.asIdeal) :
    letI := (stalkIntersectionToStalk E x hx).toAlgebra;
      IsLocalization.AtPrime (X.presheaf.stalk x) m.asIdeal := by
  let A := stalkIntersection X E
  let V := normalStalkValuationSubring X x hn hd
  let hAV : A ≤ V.toSubring :=
    iInf_le (fun y : E ↦ stalkImageSubring X y) ⟨x, hx⟩
  let : Algebra A V := (Subring.inclusion hAV).toAlgebra
  let : Algebra A (X.presheaf.stalk x) := (stalkIntersectionToStalk E x hx).toAlgebra
  have : IsLocalization.AtPrime V m.asIdeal := hloc
  let e : X.presheaf.stalk x ≃ₐ[A] V :=
    AlgEquiv.ofRingEquiv (f := normalStalkEquivValuationSubring X x hn hd) fun a ↦ by
      apply Subtype.ext
      exact algebraMap_stalkIntersectionToStalk E x hx a
  exact IsLocalization.isLocalization_of_algEquiv m.asIdeal.primeCompl e.symm

end Valuations

end Langlands.AlgebraicGeometry
