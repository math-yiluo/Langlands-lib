import Langlands.Galois.CompatibleFamily
import Langlands.Galois.FiniteField.Frobenius
import Langlands.Galois.Local.SpectralProof
import Langlands.Global.CompletionResidue

/-!
# Geometric Frobenius lifts at actual number-field completions

The lift is chosen from proved surjectivity of the spectral residue action.
Its Euler polynomial realizes the existing existential matching predicate.
-/

noncomputable section

universe uK uL uV

namespace Langlands.GaloisRepresentation

open Polynomial
open scoped Valued

variable {K : Type uK} [Field K] [NumberField K]

/-- Arithmetic Frobenius on the spectral residue field of the algebraic closure
of the actual completion. -/
def residueArithmeticFrobenius (v : Global.FinitePlace K) :
    LocalResidueClosure v ≃ₐ[
      IsLocalRing.ResidueField (LocalGalois.baseIntegers
        (Global.FiniteCompletion K v))] LocalResidueClosure v :=
  Galois.FiniteField.arithmetic
    (IsLocalRing.ResidueField (LocalGalois.baseIntegers (Global.FiniteCompletion K v)))
    (LocalResidueClosure v)

theorem residueArithmeticFrobenius_apply (v : Global.FinitePlace K)
    (x : LocalResidueClosure v) :
    residueArithmeticFrobenius v x = x ^ residueCardinality v := by
  change x ^ @Fintype.card
    (IsLocalRing.ResidueField (LocalGalois.baseIntegers (Global.FiniteCompletion K v)))
    (Fintype.ofFinite _) =
    x ^ residueCardinality v
  rw [Fintype.card_eq_nat_card, Global.CompletionResidue.card_residueField]
  rfl

/-- Surjectivity on the exact residue action used by compatible families. -/
theorem localResidueAction_surjective (v : Global.FinitePlace K) :
    Function.Surjective (localResidueAction v) := by
  let : CharZero (Global.FiniteCompletion K v) :=
    Algebra.charZero_of_charZero K (Global.FiniteCompletion K v)
  exact LocalGalois.residueHom_surjective (Global.FiniteCompletion K v)
    (AlgebraicClosure (Global.FiniteCompletion K v))

theorem exists_geometricFrobeniusLift (v : Global.FinitePlace K) :
    ∃ g : LocalGroup v, IsGeometricFrobeniusLift v g := by
  obtain ⟨g, hg⟩ := localResidueAction_surjective v (residueArithmeticFrobenius v)
  refine ⟨g⁻¹, ?_⟩
  intro x
  rw [inv_inv, hg, residueArithmeticFrobenius_apply]

/-- One geometric lift, chosen only after its existence is proved. -/
def geometricFrobeniusLift (v : Global.FinitePlace K) : LocalGroup v :=
  (exists_geometricFrobeniusLift v).choose

theorem geometricFrobeniusLift_spec (v : Global.FinitePlace K) :
    IsGeometricFrobeniusLift v (geometricFrobeniusLift v) :=
  (exists_geometricFrobeniusLift v).choose_spec

variable {L : Type uL} [Field L] [TopologicalSpace L]

/-- Evaluation at the chosen geometric lift. Its interpretation as the
unramified local Euler polynomial requires `IsUnramifiedAt`. -/
def frobeniusEulerPolynomial (A : Objects.{uK, uL, uV} K L)
    (v : Global.FinitePlace K) : L[X] :=
  eulerPolynomial (atFinitePlace v A) (geometricFrobeniusLift v)

theorem frobeniusEulerPolynomial_eq_of_lift
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K}
    (hA : IsUnramifiedAt A v) {g : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) :
    frobeniusEulerPolynomial A v = eulerPolynomial (atFinitePlace v A) g :=
  eulerPolynomial_eq_of_geometricFrobenius hA (geometricFrobeniusLift_spec v) hg

theorem hasEulerPolynomialAt_iff
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K} {P : L[X]} :
    HasEulerPolynomialAt A v P ↔
      IsUnramifiedAt A v ∧ frobeniusEulerPolynomial A v = P := by
  constructor
  · intro hA
    exact ⟨hA.1, hA.forall_lifts _ (geometricFrobeniusLift_spec v)⟩
  · rintro ⟨hur, hP⟩
    exact ⟨hur, geometricFrobeniusLift v, geometricFrobeniusLift_spec v, hP⟩

theorem IsUnramifiedAt.hasEulerPolynomialAt
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K}
    (hA : IsUnramifiedAt A v) :
    HasEulerPolynomialAt A v (frobeniusEulerPolynomial A v) :=
  hasEulerPolynomialAt_iff.mpr ⟨hA, rfl⟩

theorem HasEulerPolynomialAt.unique
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K} {P Q : L[X]}
    (hP : HasEulerPolynomialAt A v P) (hQ : HasEulerPolynomialAt A v Q) : P = Q :=
  (hasEulerPolynomialAt_iff.mp hP).2.symm.trans (hasEulerPolynomialAt_iff.mp hQ).2

theorem isUnramifiedAt_iff_existsUnique_eulerPolynomial
    {A : Objects.{uK, uL, uV} K L} {v : Global.FinitePlace K} :
    IsUnramifiedAt A v ↔ ∃! P : L[X], HasEulerPolynomialAt A v P := by
  constructor
  · intro hA
    exact ⟨frobeniusEulerPolynomial A v, hA.hasEulerPolynomialAt,
      fun _ hP => hP.unique hA.hasEulerPolynomialAt⟩
  · rintro ⟨_, hP, _⟩
    exact hP.1

section Families

variable {L : Type uL} [Field L] [NumberField L]

/-- The existing family-matching condition expressed by evaluation at the
constructed lifts, with the same exceptional sets and residue characteristics. -/
theorem matchesOutside_iff
    {excluded : Finset (Global.FinitePlace L)}
    {R : Collection.{uK, uL, uV} K L excluded}
    {S : Finset (Global.FinitePlace K)} {P : Global.FinitePlace K → L[X]} :
    MatchesOutside excluded R S P ↔
      ∀ (lam : {lam : Global.FinitePlace L // lam ∉ excluded})
        (v : Global.FinitePlace K),
        v ∉ S → residueCharacteristic v ≠ residueCharacteristic lam.val →
          IsUnramifiedAt (R lam) v ∧
            frobeniusEulerPolynomial (R lam) v =
              (P v).map (NumberField.FinitePlace.embedding lam.val) := by
  simp only [MatchesOutside, hasEulerPolynomialAt_iff]

end Families

end Langlands.GaloisRepresentation
