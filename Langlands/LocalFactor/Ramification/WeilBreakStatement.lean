import Langlands.LocalFactor.Ramification.Breaks
import Langlands.LocalFactor.Ramification.InertiaPresentation
import Langlands.VirtualRepresentation.Weil.Ramification

/-!
# Finite upper breaks and intrinsic Weil breaks

Proposition targets for arithmetic comparison, with genuine finite Galois
fields and separately quantified surjectivity evidence for each descent.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module Weil.Local
open VirtualRepresentation.LocalWeil.Ramification
open scoped BigOperators Classical

universe u v w

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Inflation along actual finite-inertia restriction preserves the full
upper-break multiplicity function and therefore its finite support. -/
def FiniteUpperBreakInflation : Prop :=
  ∀ (L M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : L ≤ M) (V : Type v) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (ρ : Representation ℂ
      (inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier) V),
    upperBreakMultiplicities (absoluteFiniteExtension F M).canonicalTopologicalData
        F.Carrier (ρ.comp (finiteInertiaRestriction F h).toMonoidHom) =
      upperBreakMultiplicities (absoluteFiniteExtension F L).canonicalTopologicalData
        F.Carrier ρ ∧
    upperBreakSupport (absoluteFiniteExtension F M).canonicalTopologicalData
        F.Carrier (ρ.comp (finiteInertiaRestriction F h).toMonoidHom) =
      upperBreakSupport (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier ρ

/-- The same comparison for a genuine presentation and its actual refinement.
Surjectivity at both fields is quantified separately from the presentation. -/
def PresentationUpperBreakRefinement : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (P : FiniteInertiaPresentation F A)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hM : Function.Surjective (weilInertiaRestriction F M)),
    let Q := P.refine M h
    upperBreakMultiplicities (absoluteFiniteExtension F Q.extension).canonicalTopologicalData
        F.Carrier (Q.representation hM) =
      upperBreakMultiplicities (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP)

/-- Any two actual finite presentations of the same Weil representation give
the same multiplicities and support. No conductor equality is a premise. -/
def PresentationUpperBreakIndependence : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (P Q : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)),
    upperBreakMultiplicities (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) =
      upperBreakMultiplicities (absoluteFiniteExtension F Q.extension).canonicalTopologicalData
        F.Carrier (Q.representation hQ) ∧
    upperBreakSupport (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) =
      upperBreakSupport (absoluteFiniteExtension F Q.extension).canonicalTopologicalData
        F.Carrier (Q.representation hQ)

/-- Isomorphic Weil representations, on independently sized carriers and with
independent finite presentations, have identical multiplicities and support. -/
def PresentationUpperBreakEquivalence : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (B : FiniteRepresentation.{0, u, w} ℂ (localWeilGroup F)),
    Nonempty (A.Equiv B) →
    ∀ (P : FiniteInertiaPresentation F A) (Q : FiniteInertiaPresentation F B)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension))
      (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)),
    upperBreakMultiplicities (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) =
      upperBreakMultiplicities (absoluteFiniteExtension F Q.extension).canonicalTopologicalData
        F.Carrier (Q.representation hQ) ∧
    upperBreakSupport (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) =
      upperBreakSupport (absoluteFiniteExtension F Q.extension).canonicalTopologicalData
        F.Carrier (Q.representation hQ)

/-- The actual rational Swan expression, coerced to the reals, is the
break-weighted multiplicity sum. The full zero coefficient contributes zero. -/
def FiniteUpperBreakWeightedSwan : Prop :=
  ∀ (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ
      (inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier) V),
    (inertiaSwanConductor (absoluteFiniteExtension F L).canonicalTopologicalData
      F.Carrier ρ : ℝ) =
      ∑ r ∈ upperBreakSupport (absoluteFiniteExtension F L).canonicalTopologicalData
        F.Carrier ρ,
        r * (upperBreakMultiplicities (absoluteFiniteExtension F L).canonicalTopologicalData
          F.Carrier ρ r : ℝ)

/-- The actual Artin expression adds the codimension of all inertia invariants
to the actual Swan expression. -/
def FiniteUpperBreakArtinIdentity : Prop :=
  ∀ (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ
      (inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier) V),
    inertiaArtinConductor (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier ρ =
      inertiaSwanConductor (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier ρ +
      (fixedCodimension
        (inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier) ρ ⊤ : ℚ)

/-- Actual fixed subspaces agree at every nonnegative upper index, including
zero. The left side uses the preimage under the actual local Weil projection. -/
def PresentationUpperFixedComparison : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (r : ℝ), 0 ≤ r →
    upperFixedSpace F A r =
      inertiaUpperFixedVectors (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) r

/-- Continuity implies actual nonempty triviality thresholds; the total real
infimum construction alone does not establish this arithmetic conclusion. -/
def WeilTrivialityThresholdsNonempty : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    A.IsContinuous → (trivialityThresholds F A).Nonempty

/-- The last break is the maximum of actual finite upper-break support.
Nonempty support is part of the conclusion, justified by positive rank. -/
def WeilLastBreakFiniteMaximum : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    A.IsContinuous → 0 < A.rank →
    ∀ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
    ∃ h : (upperBreakSupport (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP)).Nonempty,
      lastBreak F A =
        maximumUpperBreak (absoluteFiniteExtension F P.extension).canonicalTopologicalData
          F.Carrier (P.representation hP) h

/-- A Weil-irreducible representation has a single finite inertia break, of
full rank. Irreducibility of its restriction to inertia is not assumed. -/
def WeilIrreducibleUpperBreak : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    A.IsContinuous → A.IsIrreducible →
    ∀ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
    upperBreakMultiplicities (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) = Finsupp.single (lastBreak F A) A.rank ∧
    upperBreakSupport (absoluteFiniteExtension F P.extension).canonicalTopologicalData
        F.Carrier (P.representation hP) = {lastBreak F A}

/-- The actual Swan expression at every genuine finite presentation equals
rank times the intrinsic label for a continuous Weil-irreducible object. -/
def WeilIrreducibleSwanBreak : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    A.IsContinuous → A.IsIrreducible →
    ∀ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
    (P.swanConductor hP : ℝ) = (A.rank : ℝ) * lastBreak F A

/-- Left continuity gives a non-strict lower comparison and a strict upper
comparison. Both fixed-space characterizations require positive thresholds. -/
def WeilIrreduciblePositiveThresholds : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    A.IsContinuous → A.IsIrreducible →
    (∀ a : ℝ, 0 < a → (a ≤ lastBreak F A ↔ upperFixedSpace F A a = ⊥)) ∧
    (∀ b : ℝ, 0 < b → (lastBreak F A < b ↔ upperFixedSpace F A b = ⊤))

/-- A zero label means trivial action by every positive actual upper group.
The assertion includes tame, unramified, reducible and rank-zero objects. -/
def WeilLastBreakZero : Prop :=
  ∀ (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    A.IsContinuous →
    (lastBreak F A = 0 ↔ ∀ r : ℝ, 0 < r → IsTrivialAt F A r)

/-- The genuine class label describes every representative and every genuine
finite presentation. Class equality is actual Weil isomorphism-class equality;
it does not identify distinct classes with the same inertia restriction. -/
def WeilClassBreakComparison : Prop :=
  ∀ (b : VirtualRepresentation.LocalWeil.Basis.{u, v} F)
    (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)),
    FiniteRepresentation.classOf A =
      VirtualRepresentation.Weil.underlyingClass (localWeilGroup F) b →
    (trivialityThresholds F A).Nonempty ∧
    lastBreak F A = breakLabel F b ∧
    A.rank = (b.1 : ℕ) ∧
    (∀ a : ℝ, 0 < a → (a ≤ breakLabel F b ↔ upperFixedSpace F A a = ⊥)) ∧
    (∀ c : ℝ, 0 < c → (breakLabel F b < c ↔ upperFixedSpace F A c = ⊤)) ∧
    (breakLabel F b = 0 ↔ ∀ r : ℝ, 0 < r → IsTrivialAt F A r) ∧
    (∀ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
      upperBreakMultiplicities (absoluteFiniteExtension F P.extension).canonicalTopologicalData
          F.Carrier (P.representation hP) = Finsupp.single (breakLabel F b) (b.1 : ℕ) ∧
      upperBreakSupport (absoluteFiniteExtension F P.extension).canonicalTopologicalData
          F.Carrier (P.representation hP) = {breakLabel F b} ∧
      (P.swanConductor hP : ℝ) = ((b.1 : ℕ) : ℝ) * breakLabel F b)

/-- The complete comparison family for every prime and actual p-adic base,
with independent field and two representation-carrier universes. -/
def WeilBreakComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    FiniteUpperBreakInflation.{u, v} F ∧
    PresentationUpperBreakRefinement.{u, v} F ∧
    PresentationUpperBreakIndependence.{u, v} F ∧
    PresentationUpperBreakEquivalence.{u, v, w} F ∧
    FiniteUpperBreakWeightedSwan.{u, v} F ∧
    FiniteUpperBreakArtinIdentity.{u, v} F ∧
    PresentationUpperFixedComparison.{u, v} F ∧
    WeilTrivialityThresholdsNonempty.{u, v} F ∧
    WeilLastBreakFiniteMaximum.{u, v} F ∧
    WeilIrreducibleUpperBreak.{u, v} F ∧
    WeilIrreducibleSwanBreak.{u, v} F ∧
    WeilIrreduciblePositiveThresholds.{u, v} F ∧
    WeilLastBreakZero.{u, v} F ∧
    WeilClassBreakComparison.{u, v} F

end Langlands.Ramification.Padic
