import Langlands.LocalFactor.Ramification.InertiaPresentation

/-!
# Inertia surjectivity, finite presentations and conductor independence

All maps and presentations are the actual arithmetic constructions. The
declarations below are proposition targets; they do not prove the assertions.
-/

namespace Langlands.Ramification.Padic

open Weil.Local

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Absolute inertia surjects onto inertia in every actual finite Galois subfield. -/
def AbsoluteInertiaRestrictionSurjectivityStatement : Prop :=
  ∀ (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)),
    Function.Surjective (absoluteInertiaRestriction F L)

/-- The specified Weil inertia restriction is surjective at every finite subfield. -/
def WeilInertiaRestrictionSurjectivityStatement : Prop :=
  ∀ (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)),
    Function.Surjective (weilInertiaRestriction F L)

/-- Inertia restriction is surjective along every actual finite-field inclusion. -/
def FiniteInertiaRestrictionSurjectivityStatement : Prop :=
  ∀ (L M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : L ≤ M), Function.Surjective (finiteInertiaRestriction F h)

variable (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))

/-- Continuity implies finite inertia image, without finite image of the Weil group. -/
def ContinuousWeilFiniteInertiaImageStatement : Prop :=
  A.IsContinuous → A.HasFiniteInertiaImage (localInertia F)

/-- A continuous complex Weil action has a genuine kernel-defined presentation. -/
def ContinuousWeilFiniteInertiaPresentationStatement : Prop :=
  A.IsContinuous → Nonempty (FiniteInertiaPresentation F A)

/-- Enlarging the presenting finite field preserves both conductor expressions. -/
def FiniteInertiaConductorRefinementStatement : Prop :=
  ∀ (P : FiniteInertiaPresentation F A)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hM : Function.Surjective (weilInertiaRestriction F M)),
    (P.refine M h).artinConductor hM = P.artinConductor hP ∧
    (P.refine M h).swanConductor hM = P.swanConductor hP

/-- The published pullbacks to the actual compositum preserve the two sums. -/
def FiniteInertiaConductorCompositumStatement : Prop :=
  ∀ (P Q : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)),
    let R := FiniteInertiaCommonRefinement.compositum F A P Q
    let T := (absoluteFiniteExtension F R.extension).canonicalTopologicalData
    inertiaArtinConductor T F.Carrier (R.leftRepresentation hP) =
        P.artinConductor hP ∧
    inertiaSwanConductor T F.Carrier (R.leftRepresentation hP) =
        P.swanConductor hP ∧
    inertiaArtinConductor T F.Carrier (R.rightRepresentation hQ) =
        Q.artinConductor hQ ∧
    inertiaSwanConductor T F.Carrier (R.rightRepresentation hQ) =
        Q.swanConductor hQ

/-- Any two genuine presentations of the same Weil action give the same sums. -/
def FiniteInertiaConductorIndependenceStatement : Prop :=
  ∀ (P Q : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)),
    P.artinConductor hP = Q.artinConductor hQ ∧
    P.swanConductor hP = Q.swanConductor hQ

/-- Actual equivalence preserves conductors across independent carrier universes
and arbitrary genuine presentations of the two actions. -/
def FiniteInertiaConductorEquivalenceStatement
    (B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)) : Prop :=
  ∀ (_e : FiniteRepresentation.Equiv A B)
    (P : FiniteInertiaPresentation F A) (Q : FiniteInertiaPresentation F B)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)),
    P.artinConductor hP = Q.artinConductor hQ ∧
    P.swanConductor hP = Q.swanConductor hQ

/-- The complete family over all primes, p-adic fields and finite-dimensional
complex Weil actions, with independent field and two carrier universes. -/
def InertiaSurjectivityPresentationAndConductorIndependenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    AbsoluteInertiaRestrictionSurjectivityStatement F ∧
    WeilInertiaRestrictionSurjectivityStatement F ∧
    FiniteInertiaRestrictionSurjectivityStatement F ∧
    (∀ (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)),
      ContinuousWeilFiniteInertiaImageStatement F A ∧
      ContinuousWeilFiniteInertiaPresentationStatement F A ∧
      FiniteInertiaConductorRefinementStatement F A ∧
      FiniteInertiaConductorCompositumStatement F A ∧
      FiniteInertiaConductorIndependenceStatement F A) ∧
    (∀ (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
      (B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)),
      FiniteInertiaConductorEquivalenceStatement F A B)

end Langlands.Ramification.Padic
