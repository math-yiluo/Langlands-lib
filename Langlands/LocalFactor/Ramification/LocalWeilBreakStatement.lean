import Langlands.LocalFactor.Ramification.Breaks
import Langlands.LocalFactor.Ramification.InertiaPresentation
import Langlands.VirtualRepresentation.Weil.Ramification

/-!
# Finite upper breaks and intrinsic Weil breaks over local fields

Proposition targets using the finite upper-break data and the intrinsic Weil
filtration over a specified separable closure of a nonarchimedean local field.
-/

namespace Langlands.Ramification.Local

open VirtualRepresentation.LocalWeil.SepClosed.Ramification
open scoped Classical

universe uK uΩ uV uW

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω]

local notation "finiteData" => SepClosed.finiteTopologicalData K Ω

/-- Inflation along finite inertia restriction preserves the multiplicity function
and its finite support. -/
def FiniteUpperBreakInflation [IsSepClosure K Ω] : Prop :=
  ∀ (L M : FiniteGaloisIntermediateField K Ω)
    (h : L ≤ M) (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (inertia (finiteData L) K) V),
    let inflated := ρ.comp (SepClosed.finiteInertiaRestriction K Ω h).toMonoidHom
    upperBreakMultiplicities (finiteData M) K inflated =
      upperBreakMultiplicities (finiteData L) K ρ ∧
    upperBreakSupport (finiteData M) K inflated = upperBreakSupport (finiteData L) K ρ

/-- The rational Swan conductor, coerced to the reals, is the sum of upper
breaks weighted by their multiplicities. -/
def FiniteUpperBreakWeightedSwan [IsSepClosure K Ω] : Prop :=
  ∀ (L : FiniteGaloisIntermediateField K Ω)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (inertia (finiteData L) K) V),
    (inertiaSwanConductor (finiteData L) K ρ : ℝ) =
      ∑ r ∈ upperBreakSupport (finiteData L) K ρ,
        r * (upperBreakMultiplicities (finiteData L) K ρ r : ℝ)

/-- The Artin conductor is the Swan conductor plus the codimension of all
inertia invariants. -/
def FiniteUpperBreakArtinIdentity [IsSepClosure K Ω] : Prop :=
  ∀ (L : FiniteGaloisIntermediateField K Ω)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (inertia (finiteData L) K) V),
    inertiaArtinConductor (finiteData L) K ρ =
      inertiaSwanConductor (finiteData L) K ρ +
      (fixedCodimension (inertia (finiteData L) K) ρ ⊤ : ℚ)

variable [IsSepClosure K Ω]

local notation "W" =>
  (@Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- Refining a presentation preserves multiplicities, with surjectivity supplied
separately at the original and enlarged fields. -/
def PresentationUpperBreakRefinement : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (M : FiniteGaloisIntermediateField K Ω)
    (h : P.extension ≤ M)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hM : Function.Surjective (SepClosed.weilInertiaRestriction K Ω M)),
    let Q := P.refine M h
    upperBreakMultiplicities (finiteData Q.extension) K (Q.representation hM) =
      upperBreakMultiplicities (finiteData P.extension) K (P.representation hP)

/-- Every two presentations of the same Weil action have the same multiplicities
and support. -/
def PresentationUpperBreakIndependence : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (P Q : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hQ : Function.Surjective (SepClosed.weilInertiaRestriction K Ω Q.extension)),
    upperBreakMultiplicities (finiteData P.extension) K (P.representation hP) =
      upperBreakMultiplicities (finiteData Q.extension) K (Q.representation hQ) ∧
    upperBreakSupport (finiteData P.extension) K (P.representation hP) =
      upperBreakSupport (finiteData Q.extension) K (Q.representation hQ)

/-- Isomorphic Weil actions on independent carriers have identical multiplicities
and support at all presentations. -/
def PresentationUpperBreakEquivalence : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (B : FiniteRepresentation.{0, uΩ, uW} ℂ W),
    Nonempty (A.Equiv B) →
    ∀ (P : SepClosed.FiniteInertiaPresentation K Ω A)
      (Q : SepClosed.FiniteInertiaPresentation K Ω B)
      (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
      (hQ : Function.Surjective (SepClosed.weilInertiaRestriction K Ω Q.extension)),
    upperBreakMultiplicities (finiteData P.extension) K (P.representation hP) =
      upperBreakMultiplicities (finiteData Q.extension) K (Q.representation hQ) ∧
    upperBreakSupport (finiteData P.extension) K (P.representation hP) =
      upperBreakSupport (finiteData Q.extension) K (Q.representation hQ)

/-- The Weil upper fixed space agrees with the presented inertia fixed space
at every nonnegative upper index. -/
def PresentationUpperFixedComparison : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (r : ℝ), 0 ≤ r →
    upperFixedSpace K Ω A r =
      inertiaUpperFixedVectors (finiteData P.extension) K (P.representation hP) r

/-- A continuous Weil action is trivial at some nonnegative upper index. -/
def WeilTrivialityThresholdsNonempty : Prop :=
  ∀ A : FiniteRepresentation.{0, uΩ, uV} ℂ W,
    A.IsContinuous → (trivialityThresholds K Ω A).Nonempty

/-- For a continuous, positive-rank Weil action, every finite presentation has
nonempty support with maximum equal to the intrinsic last break. -/
def WeilLastBreakFiniteMaximum : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W),
    A.IsContinuous → 0 < A.rank →
    ∀ (P : SepClosed.FiniteInertiaPresentation K Ω A)
      (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension)),
    ∃ h : (upperBreakSupport (finiteData P.extension) K (P.representation hP)).Nonempty,
      lastBreak K Ω A = maximumUpperBreak (finiteData P.extension) K (P.representation hP) h

/-- A continuous Weil-irreducible action has a single upper break, of full rank,
at every finite inertia presentation. -/
def WeilIrreducibleUpperBreak : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W),
    A.IsContinuous → A.IsIrreducible →
    ∀ (P : SepClosed.FiniteInertiaPresentation K Ω A)
      (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension)),
    upperBreakMultiplicities (finiteData P.extension) K (P.representation hP) =
      Finsupp.single (lastBreak K Ω A) A.rank ∧
    upperBreakSupport (finiteData P.extension) K (P.representation hP) = {lastBreak K Ω A}

/-- The Swan conductor of a continuous Weil-irreducible action at every
presentation is its rank times its last break. -/
def WeilIrreducibleSwanBreak : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W),
    A.IsContinuous → A.IsIrreducible →
    ∀ (P : SepClosed.FiniteInertiaPresentation K Ω A)
      (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension)),
    (P.swanConductor hP : ℝ) = (A.rank : ℝ) * lastBreak K Ω A

/-- At positive indices, Weil-irreducible actions have zero fixed space through
the last break and full fixed space strictly above it. -/
def WeilIrreduciblePositiveThresholds : Prop :=
  ∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W),
    A.IsContinuous → A.IsIrreducible →
    (∀ a : ℝ, 0 < a → (a ≤ lastBreak K Ω A ↔ upperFixedSpace K Ω A a = ⊥)) ∧
    (∀ b : ℝ, 0 < b → (lastBreak K Ω A < b ↔ upperFixedSpace K Ω A b = ⊤))

/-- The last break of a continuous action is zero exactly when every positive
upper group acts trivially. -/
def WeilLastBreakZero : Prop :=
  ∀ A : FiniteRepresentation.{0, uΩ, uV} ℂ W,
    A.IsContinuous →
    (lastBreak K Ω A = 0 ↔ ∀ r : ℝ, 0 < r → IsTrivialAt K Ω A r)

/-- The intrinsic label and rank of a Weil basis class govern the fixed spaces,
upper-break multiplicities and Swan conductor of every representative. -/
def WeilClassBreakComparison : Prop :=
  ∀ (b : VirtualRepresentation.LocalWeil.SepClosed.Basis.{uK, uΩ, uV} K Ω)
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W),
    FiniteRepresentation.classOf A = VirtualRepresentation.Weil.underlyingClass W b →
    (trivialityThresholds K Ω A).Nonempty ∧
    lastBreak K Ω A = breakLabel K Ω b ∧
    A.rank = (b.1 : ℕ) ∧
    (∀ a : ℝ, 0 < a → (a ≤ breakLabel K Ω b ↔ upperFixedSpace K Ω A a = ⊥)) ∧
    (∀ c : ℝ, 0 < c → (breakLabel K Ω b < c ↔ upperFixedSpace K Ω A c = ⊤)) ∧
    (breakLabel K Ω b = 0 ↔ ∀ r : ℝ, 0 < r → IsTrivialAt K Ω A r) ∧
    (∀ (P : SepClosed.FiniteInertiaPresentation K Ω A)
      (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension)),
      upperBreakMultiplicities (finiteData P.extension) K (P.representation hP) =
        Finsupp.single (breakLabel K Ω b) (b.1 : ℕ) ∧
      upperBreakSupport (finiteData P.extension) K (P.representation hP) = {breakLabel K Ω b} ∧
      (P.swanConductor hP : ℝ) = ((b.1 : ℕ) : ℝ) * breakLabel K Ω b)

/-- The fourteen clauses over all local fields and separable closures, with
independent universes for the field, closure and both representation carriers. -/
def WeilBreakComparisonStatement : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
    FiniteUpperBreakInflation.{uK, uΩ, uV} K Ω ∧
    PresentationUpperBreakRefinement.{uK, uΩ, uV} K Ω ∧
    PresentationUpperBreakIndependence.{uK, uΩ, uV} K Ω ∧
    PresentationUpperBreakEquivalence.{uK, uΩ, uV, uW} K Ω ∧
    FiniteUpperBreakWeightedSwan.{uK, uΩ, uV} K Ω ∧
    FiniteUpperBreakArtinIdentity.{uK, uΩ, uV} K Ω ∧
    PresentationUpperFixedComparison.{uK, uΩ, uV} K Ω ∧
    WeilTrivialityThresholdsNonempty.{uK, uΩ, uV} K Ω ∧
    WeilLastBreakFiniteMaximum.{uK, uΩ, uV} K Ω ∧
    WeilIrreducibleUpperBreak.{uK, uΩ, uV} K Ω ∧
    WeilIrreducibleSwanBreak.{uK, uΩ, uV} K Ω ∧
    WeilIrreduciblePositiveThresholds.{uK, uΩ, uV} K Ω ∧
    WeilLastBreakZero.{uK, uΩ, uV} K Ω ∧
    WeilClassBreakComparison.{uK, uΩ, uV} K Ω

end Langlands.Ramification.Local
