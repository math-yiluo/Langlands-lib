import Langlands.WeilDeligne.Parameters
import Mathlib.LinearAlgebra.Determinant

/-!
# Frobenius correction and semisimplification targets

These are proposition definitions, not proofs. They use the actual algebraic
WD pairs, topology predicates, and Frobenius-semisimplicity predicate of the
companion framework. No canonical correction or classification is assumed.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.Frobenius

universe uG uV uW uX

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- The normalization needed by the correction theorem: geometric degree `+1`
has norm `q⁻¹`, with `q > 1`. Surjectivity is stated separately in the targets. -/
def NormCompatible (degree : G →* Multiplicative ℤ) (q : ℕ) : Prop :=
  1 < q ∧ ∀ g, (ν g : ℂ) = (q : ℂ) ^ (-Multiplicative.toAdd (degree g))

/-- The actual nilpotent exponential, using dimension as a truncation bound. -/
def monodromyExponential (A : WeilDeligneRepresentation ℂ G ν) (a : ℂ) :
    Module.End ℂ A :=
  ∑ j ∈ Finset.range (Module.finrank ℂ A),
    ((a ^ j) / (Nat.factorial j : ℂ)) • A.monodromy ^ j

/-- A candidate unipotent part at a chosen geometric Frobenius. -/
def IsCorrectionAt (A : WeilDeligneRepresentation ℂ G ν) (Phi : G)
    (u : A ≃ₗ[ℂ] A) : Prop :=
  IsNilpotent (u.toLinearMap - 1) ∧
  Commute u.toLinearMap A.monodromy ∧
  (∀ g, Commute u.toLinearMap (A.representation g)) ∧
  Module.End.IsSemisimple (A.representation Phi * u.symm.toLinearMap)

/-- Tate's choice-free characterization, including every exponential parameter
and every nonzero degree. -/
def IsCorrection (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation ℂ G ν) (u : A ≃ₗ[ℂ] A) : Prop :=
  IsNilpotent (u.toLinearMap - 1) ∧
  Commute u.toLinearMap A.monodromy ∧
  (∀ g, Commute u.toLinearMap (A.representation g)) ∧
  ∀ g, Multiplicative.toAdd (degree g) ≠ 0 → ∀ a : ℂ,
    Module.End.IsSemisimple (monodromyExponential A a * A.representation g *
      (u ^ (-Multiplicative.toAdd (degree g))).toLinearMap)

/-- Semisimplification on the same carrier with literally unchanged monodromy.
The candidate is an actual representation, not an arbitrary function. -/
def IsSemisimplificationOn (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation ℂ G ν) (s : Representation ℂ G A) : Prop :=
  ∃ u : A ≃ₗ[ℂ] A, IsCorrection degree A u ∧
    ∀ g, s g = A.representation g * (u ^ (-Multiplicative.toAdd (degree g))).toLinearMap

/-- The same relation after a specified identification of carrier vector spaces.
The identification intertwines the corrected action, not the original action. -/
def IsSemisimplificationAlong (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (e : A ≃ₗ[ℂ] B) : Prop :=
  e.toLinearMap.comp A.monodromy = B.monodromy.comp e.toLinearMap ∧
  ∃ u : A ≃ₗ[ℂ] A, IsCorrection degree A u ∧
    ∀ g, e.toLinearMap.comp
      (A.representation g * (u ^ (-Multiplicative.toAdd (degree g))).toLinearMap) =
      (B.representation g).comp e.toLinearMap

/-- Semisimplification of actual WD pairs, up to a genuine carrier identification. -/
def IsSemisimplification (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) : Prop :=
  ∃ e : A ≃ₗ[ℂ] B, IsSemisimplificationAlong degree A B e

/-- Existence and uniqueness of the correction, with no assumed output. -/
def CorrectionExistence : Prop :=
  ∀ (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → NormCompatible (ν := ν) degree q →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      (∃! u : A ≃ₗ[ℂ] A, IsCorrection degree A u) ∧
      (∀ Phi, Multiplicative.toAdd (degree Phi) = 1 →
        ∃! u : A ≃ₗ[ℂ] A, IsCorrectionAt A Phi u)

/-- The unipotent part is independent of the geometric Frobenius lift.
The corresponding corrected action is therefore equal on the fixed carrier. -/
def ChoiceIndependence : Prop :=
  ∀ (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → NormCompatible (ν := ν) degree q →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      (∀ Phi, Multiplicative.toAdd (degree Phi) = 1 → ∀ u : A ≃ₗ[ℂ] A,
        IsCorrectionAt A Phi u ↔ IsCorrection degree A u) ∧
      (∀ Phi Psi, Multiplicative.toAdd (degree Phi) = 1 →
        Multiplicative.toAdd (degree Psi) = 1 → ∀ u v : A ≃ₗ[ℂ] A,
          IsCorrectionAt A Phi u → IsCorrectionAt A Psi v →
          u = v ∧ ∀ g,
            A.representation g * (u ^ (-Multiplicative.toAdd (degree g))).toLinearMap =
            A.representation g * (v ^ (-Multiplicative.toAdd (degree g))).toLinearMap)

/-- Actual corrected representations exist, uniquely on the original carrier.
Their WD covariance is a conclusion, so a pair can be assembled honestly. -/
def SameCarrierExistence : Prop :=
  ∀ (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → NormCompatible (ν := ν) degree q →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      (∃! s : Representation ℂ G A, IsSemisimplificationOn degree A s) ∧
      (∀ s : Representation ℂ G A, IsSemisimplificationOn degree A s →
        (FiniteRepresentation.of s).HasFiniteInertiaImage degree.ker ∧
        (∀ g, Multiplicative.toAdd (degree g) ≠ 0 → Module.End.IsSemisimple (s g)) ∧
        ∀ g, s g * A.monodromy * s g⁻¹ = (ν g : ℂ) • A.monodromy)

/-- Existence of an actual semisimplified WD pair with the same carrier universe. -/
def PairExistence : Prop :=
  ∀ (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → NormCompatible (ν := ν) degree q →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      ∃ B : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
        IsSemisimplification degree A B ∧ B.IsFrobeniusSemisimple degree ∧
        B.toFiniteRepresentation.HasFiniteInertiaImage degree.ker

/-- Uniqueness across different carrier spaces is genuine pair isomorphism. -/
def PairUniqueness : Prop :=
  ∀ (degree : G →* Multiplicative ℤ),
    Function.Surjective degree →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
      (C : WeilDeligneRepresentation.{0, uG, uX} ℂ G ν),
      IsSemisimplification degree A B → IsSemisimplification degree A C →
      Nonempty (Equiv B C)

/-- Fixed points and idempotence use the existing Frobenius-semisimplicity
predicate; nonzero monodromy is allowed. -/
def Idempotence : Prop :=
  ∀ (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → NormCompatible (ν := ν) degree q →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      (IsSemisimplificationOn degree A A.representation ↔
        A.IsFrobeniusSemisimple degree) ∧
      (∀ B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν,
        IsSemisimplification degree A B → IsSemisimplification degree B B)

/-- Ordinary semisimplicity here concerns the underlying Weil representation. -/
def WeilSemisimplicityComparison : Prop :=
  ∀ (degree : G →* Multiplicative ℤ),
    Function.Surjective degree →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      (A.toFiniteRepresentation.IsSemisimple ↔ A.IsFrobeniusSemisimple degree)

/-- Every original intertwiner also intertwines the unipotent corrections. -/
def CorrectionNaturality : Prop :=
  ∀ (degree : G →* Multiplicative ℤ),
    Function.Surjective degree →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
      (u : A ≃ₗ[ℂ] A) (v : B ≃ₗ[ℂ] B),
      IsCorrection degree A u → IsCorrection degree B v → ∀ f : Hom A B,
        f.intertwiner.toLinearMap.comp u.toLinearMap =
          v.toLinearMap.comp f.intertwiner.toLinearMap

/-- All original WD morphisms remain morphisms between the corrected actions.
This does not assert that every new morphism comes from an original one. -/
def MorphismCompatibility : Prop :=
  ∀ (degree : G →* Multiplicative ℤ),
    Function.Surjective degree →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
      (s : Representation ℂ G A) (t : Representation ℂ G B),
      IsSemisimplificationOn degree A s → IsSemisimplificationOn degree B t →
      ∀ f : Hom A B, ∀ g,
        f.intertwiner.toLinearMap.comp (s g) = (t g).comp f.intertwiner.toLinearMap

/-- Transport of input and output by genuine pair isomorphisms preserves the relation. -/
def IsomorphismCompatibility : Prop :=
  ∀ (degree : G →* Multiplicative ℤ),
    ∀ (A A' : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B B' : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
      Equiv A A' → Equiv B B' →
      (IsSemisimplification degree A B ↔ IsSemisimplification degree A' B')

/-- The carrier identification transports exactly every monodromy power kernel
and image. Inertia actions and determinants are also preserved. -/
def Invariants : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (e : A ≃ₗ[ℂ] B),
    IsSemisimplificationAlong degree A B e →
    A.rank = B.rank ∧
    e.toLinearMap.comp A.monodromy = B.monodromy.comp e.toLinearMap ∧
    (∀ n : ℕ,
      (LinearMap.ker (A.monodromy ^ n)).map e.toLinearMap =
        LinearMap.ker (B.monodromy ^ n)) ∧
    (∀ n : ℕ,
      (LinearMap.range (A.monodromy ^ n)).map e.toLinearMap =
        LinearMap.range (B.monodromy ^ n)) ∧
    Module.finrank ℂ (LinearMap.ker A.monodromy) =
      Module.finrank ℂ (LinearMap.ker B.monodromy) ∧
    Module.finrank ℂ (LinearMap.range A.monodromy) =
      Module.finrank ℂ (LinearMap.range B.monodromy) ∧
    (∀ g, Multiplicative.toAdd (degree g) = 0 →
      e.toLinearMap.comp (A.representation g) = (B.representation g).comp e.toLinearMap) ∧
    ∀ g, LinearMap.det (A.representation g) = LinearMap.det (B.representation g)

/-- Nonzero scaling of monodromy is implemented by an actual linear
automorphism centralizing the Weil action. The scalar zero is excluded. -/
def NonzeroMonodromyScaling : Prop :=
  ∀ (degree : G →* Multiplicative ℤ) (q : ℕ),
    Function.Surjective degree → NormCompatible (ν := ν) degree q →
    ∀ A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν,
      A.toFiniteRepresentation.HasFiniteInertiaImage degree.ker →
      ∀ a : ℂ, a ≠ 0 → ∃ e : A ≃ₗ[ℂ] A,
        (∀ g, Commute e.toLinearMap (A.representation g)) ∧
        e.toLinearMap.comp A.monodromy = (a • A.monodromy).comp e.toLinearMap

/-- Whole algebraic correction and semisimplification statement family. -/
def AlgebraicFamily : Prop :=
  CorrectionExistence.{uG, uV} (ν := ν) ∧
  ChoiceIndependence.{uG, uV} (ν := ν) ∧
  SameCarrierExistence.{uG, uV} (ν := ν) ∧
  PairExistence.{uG, uV} (ν := ν) ∧
  PairUniqueness.{uG, uV, uW, uX} (ν := ν) ∧
  Idempotence.{uG, uV, uW} (ν := ν) ∧
  WeilSemisimplicityComparison.{uG, uV} (ν := ν) ∧
  CorrectionNaturality.{uG, uV, uW} (ν := ν) ∧
  MorphismCompatibility.{uG, uV, uW} (ν := ν) ∧
  IsomorphismCompatibility.{uG, uV, uW} (ν := ν) ∧
  Invariants.{uG, uV, uW} (ν := ν) ∧
  NonzeroMonodromyScaling.{uG, uV} (ν := ν)

section Topology

variable [TopologicalSpace G]

/-- Open inertia kernel is preserved without identifying it with continuity. -/
def ParameterPreservation : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    IsSemisimplification degree A B → (IsParameter degree.ker A ↔ IsParameter degree.ker B)

/-- With continuous degree, the actual usual-complex-topology continuity
condition is preserved. No finite-image-to-continuity implication is used. -/
def ContinuityPreservation : Prop :=
  ∀ (degree : G →* Multiplicative ℤ),
    Continuous degree →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
      IsSemisimplification degree A B → (A.IsContinuous ↔ B.IsContinuous)

/-- Whole target, including preservation of both distinct parameter conditions. -/
def Statement : Prop :=
  AlgebraicFamily.{uG, uV, uW, uX} (ν := ν) ∧
  ParameterPreservation.{uG, uV, uW} (ν := ν) ∧
  ContinuityPreservation.{uG, uV, uW} (ν := ν)

end Topology

end Langlands.WeilDeligneRepresentation.Frobenius
