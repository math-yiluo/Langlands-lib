import Langlands.LocalFactor.Ramification.InertiaPresentation

/-!
# Inertia surjectivity, presentations and conductors over local fields

Proposition targets over a specified separable closure of a nonarchimedean
local field, using the published arithmetic restrictions and presentations.
-/

namespace Langlands.Ramification.Local

universe uK uΩ uV uW

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω]

/-- Inertia restriction is surjective along every finite Galois subfield inclusion. -/
def FiniteInertiaRestrictionSurjectivityStatement [IsSepClosure K Ω] : Prop :=
  ∀ (L M : FiniteGaloisIntermediateField K Ω)
    (h : L ≤ M), Function.Surjective (SepClosed.finiteInertiaRestriction K Ω h)

variable [IsSepClosure K Ω]

local notation "W[" K ", " Ω "]" =>
  (@Weil.Local.SepClosed.localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- Absolute inertia surjects onto inertia in each finite Galois subextension. -/
def AbsoluteInertiaRestrictionSurjectivityStatement : Prop :=
  ∀ L : FiniteGaloisIntermediateField K Ω,
    Function.Surjective (SepClosed.absoluteInertiaRestriction K Ω L)

/-- Weil inertia surjects onto inertia in each finite Galois subextension. -/
def WeilInertiaRestrictionSurjectivityStatement : Prop :=
  ∀ L : FiniteGaloisIntermediateField K Ω,
    Function.Surjective (SepClosed.weilInertiaRestriction K Ω L)

/-- A continuous complex Weil representation has finite inertia image. -/
def ContinuousWeilFiniteInertiaImageStatement
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω]) : Prop :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  A.IsContinuous → A.HasFiniteInertiaImage (Weil.Local.SepClosed.localInertia K Ω)

/-- A continuous complex Weil representation has a finite inertia presentation. -/
def ContinuousWeilFiniteInertiaPresentationStatement
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω]) : Prop :=
  A.IsContinuous → Nonempty (SepClosed.FiniteInertiaPresentation K Ω A)

/-- Enlarging the presenting field preserves the Artin and Swan conductors. -/
def FiniteInertiaConductorRefinementStatement
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω]) : Prop :=
  ∀ (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (M : FiniteGaloisIntermediateField K Ω)
    (h : P.extension ≤ M)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hM : Function.Surjective (SepClosed.weilInertiaRestriction K Ω M)),
    (P.refine M h).artinConductor hM = P.artinConductor hP ∧
    (P.refine M h).swanConductor hM = P.swanConductor hP

/-- Each pullback to the compositum preserves the two conductors of its presentation. -/
def FiniteInertiaConductorCompositumStatement
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω]) : Prop :=
  ∀ (P Q : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hQ : Function.Surjective (SepClosed.weilInertiaRestriction K Ω Q.extension)),
    let R := SepClosed.FiniteInertiaCommonRefinement.compositum K Ω A P Q
    let T := SepClosed.finiteTopologicalData K Ω R.extension
    inertiaArtinConductor T K (R.leftRepresentation hP) = P.artinConductor hP ∧
    inertiaSwanConductor T K (R.leftRepresentation hP) = P.swanConductor hP ∧
    inertiaArtinConductor T K (R.rightRepresentation hQ) = Q.artinConductor hQ ∧
    inertiaSwanConductor T K (R.rightRepresentation hQ) = Q.swanConductor hQ

/-- The Artin and Swan conductors agree at every pair of presentations of the same action. -/
def FiniteInertiaConductorIndependenceStatement
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω]) : Prop :=
  ∀ (P Q : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hQ : Function.Surjective (SepClosed.weilInertiaRestriction K Ω Q.extension)),
    P.artinConductor hP = Q.artinConductor hQ ∧
    P.swanConductor hP = Q.swanConductor hQ

/-- A Weil intertwiner that is a linear equivalence preserves both conductors across
independent carrier universes and arbitrary presentations. -/
def FiniteInertiaConductorEquivalenceStatement
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω])
    (B : FiniteRepresentation.{0, uΩ, uW} ℂ W[K, Ω]) : Prop :=
  ∀ (_e : FiniteRepresentation.Equiv A B)
    (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (Q : SepClosed.FiniteInertiaPresentation K Ω B)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hQ : Function.Surjective (SepClosed.weilInertiaRestriction K Ω Q.extension)),
    P.artinConductor hP = Q.artinConductor hQ ∧
    P.swanConductor hP = Q.swanConductor hQ

/-- The nine clauses over all local fields and separable closures, with independent
universes for the field, closure and both representation carriers. -/
def InertiaSurjectivityPresentationAndConductorIndependenceStatement : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
    AbsoluteInertiaRestrictionSurjectivityStatement K Ω ∧
    WeilInertiaRestrictionSurjectivityStatement K Ω ∧
    FiniteInertiaRestrictionSurjectivityStatement K Ω ∧
    (∀ A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω],
      ContinuousWeilFiniteInertiaImageStatement.{uK, uΩ, uV} K Ω A ∧
      ContinuousWeilFiniteInertiaPresentationStatement.{uK, uΩ, uV} K Ω A ∧
      FiniteInertiaConductorRefinementStatement.{uK, uΩ, uV} K Ω A ∧
      FiniteInertiaConductorCompositumStatement.{uK, uΩ, uV} K Ω A ∧
      FiniteInertiaConductorIndependenceStatement.{uK, uΩ, uV} K Ω A) ∧
    (∀ (A : FiniteRepresentation.{0, uΩ, uV} ℂ W[K, Ω])
      (B : FiniteRepresentation.{0, uΩ, uW} ℂ W[K, Ω]),
      FiniteInertiaConductorEquivalenceStatement.{uK, uΩ, uV, uW} K Ω A B)

end Langlands.Ramification.Local
