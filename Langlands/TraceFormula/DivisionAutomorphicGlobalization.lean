import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.HeckeCharacter
import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Representation.CompactCoefficient.Classes

/-! # Prescribing local factors of automorphic representations of division algebra units -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj Pointwise TensorProduct
open Langlands.Global Langlands.Global.RestrictionSplitCentre Langlands.GroupScheme

namespace Langlands.TraceFormula

variable (K A : Type) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

set_option hygiene false in
local notation "Gₐ" => FiniteAlgebraUnits.groupScheme (Module.finBasis K A)

/-- Scalar units inside the actual coefficient points of the algebra's unit group scheme. -/
def algebraUnitsScalar (R : CommAlgCat (CommRingCat.of K)) :
    Rˣ →* (Gₐ).affinePoints R :=
  (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A) R).symm.toMonoidHom.comp
    (Units.map (algebraMap R (R ⊗[K] A)))

set_option maxHeartbeats 800000 in
/-- Simultaneous occurrence of prescribed local representations with coefficients
compact modulo scalars in one automorphic summand of a division algebra's unit group.
The local scalar characters are those of the supplied finite-order Hecke character. -/
def DivisionAutomorphicGlobalizationStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (A : Type) [DivisionRing A] [Algebra K A] [FiniteDimensional K A] [Algebra.IsCentral K A]
    (hG : IsConnectedReductive Gₐ), CompactSpace (CanonicalQuotient K Gₐ) →
    ∀ (ω : HeckeCharacter K), ω.HasFiniteOrder →
    ∀ (S : Finset (Langlands.Global.FinitePlace K)),
    let H (v : S) := PlaceGroupPoints K Gₐ (.inr v.val)
    let scalar (v : S) : (FiniteCompletion K v.val)ˣ →* H v :=
      algebraUnitsScalar K A (CommAlgCat.of K (FiniteCompletion K v.val))
    ∀ (V : S → Type) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
      (ρ : ∀ v, Representation ℂ (H v) (V v)),
      (∀ v, (ρ v).IsIrreducible ∧ IsAdmissible (ρ v)) →
      (∀ (v : S) (t : (FiniteCompletion K v.val)ˣ),
        ρ v (scalar v t) = (ω.finiteComponent v.val t : ℂ) • 1) →
      (∀ v (x : V v) (ℓ : Module.Dual ℂ (V v)), IsSmoothVector (ρ v).dual ℓ →
        ∃ C : Set (H v), IsCompact C ∧
          Function.support (matrixCoefficient (ρ v) ℓ x) ⊆ C * (scalar v).range) →
    let E := Lp ℂ 2 (canonicalMeasure K Gₐ)
    let π := canonicalL2RightAction K Gₐ centralSplitTorusCharacter hG
    let scalarAdelic := algebraUnitsScalar K A (CommAlgCat.of K (AdeleRing (𝓞 K) K))
    ∃ P : Submodule ℂ E, P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
      (∀ a x, x ∈ P → π a x ∈ P) ∧
      (∀ Q : Submodule ℂ E, Q ≤ P → IsClosed (Q : Set E) →
        (∀ a x, x ∈ Q → π a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      (∀ (t : Ideles K) x, x ∈ P → π (scalarAdelic t) x = (ω.onIdeles t : ℂ) • x) ∧
      ∀ v, ∃ j : V v →ₗ[ℂ] P, j ≠ 0 ∧ ∀ g x,
        (j (ρ v g x) : E) = π (AdelicGroupPoints.ofPlace K Gₐ (.inr v.val) g) (j x)

end Langlands.TraceFormula
