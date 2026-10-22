import Langlands.VirtualRepresentation.Integral

/-!
# Integral relation descent and extraction of positive basis elements

Proposition definitions for the elementary integral-lattice steps in
Henniart 2000, sections 2.5-2.8. The source and target are actual Finsupp
modules with their coefficient pairings. Their representation-theoretic
instantiations, and the equality of generator pairings, are separate inputs.
-/

noncomputable section

namespace Langlands.VirtualRepresentation

universe u v w

/-- The integral coefficient pairing is positive definite. -/
def IntegralPairingDefinitenessStatement (ι : Type u) : Prop :=
  ∀ x : IntegralLattice ι,
    0 ≤ pairing x x ∧ (pairing x x = 0 ↔ x = 0)

/-- Equality of generator pairings gives exactly the same integral relations.
It does not assume any map between the generated lattices. -/
def IntegralRelationDescentStatement (ι : Type u) (κ : Type v) (J : Type w) : Prop :=
  ∀ (left : J → IntegralLattice ι) (right : J → IntegralLattice κ),
    (∀ j k, pairing (left j) (left k) = pairing (right j) (right k)) →
    relations left = relations right

/-- Equal integral relations yield the unique isomorphism of the two spans
that maps every specified generator to its partner. -/
def IntegralGeneratedEquivalenceStatement (ι : Type u) (κ : Type v) (J : Type w) : Prop :=
  ∀ (left : J → IntegralLattice ι) (right : J → IntegralLattice κ),
    relations left = relations right →
    ∃! T : generated left ≃ₗ[ℤ] generated right,
      ∀ j, T (evaluateGenerators left (generator j)) =
        evaluateGenerators right (generator j)

/-- A map on the generated lattices which respects paired generators
preserves their coefficient pairings if those pairings agree on generators. -/
def IntegralGeneratedIsometryStatement (ι : Type u) (κ : Type v) (J : Type w) : Prop :=
  ∀ (left : J → IntegralLattice ι) (right : J → IntegralLattice κ),
    (∀ j k, pairing (left j) (left k) = pairing (right j) (right k)) →
    ∀ T : generated left →ₗ[ℤ] generated right,
      (∀ j, T (evaluateGenerators left (generator j)) =
        evaluateGenerators right (generator j)) →
      ∀ x y : generated left,
        pairing (T x : IntegralLattice κ) (T y : IntegralLattice κ) =
          pairing (x : IntegralLattice ι) (y : IntegralLattice ι)

/-- Equality of the degrees of paired generators descends to their spans. -/
def IntegralGeneratedDegreeStatement (ι : Type u) (κ : Type v) (J : Type w) : Prop :=
  ∀ (left : J → IntegralLattice ι) (right : J → IntegralLattice κ)
    (sourceWeight : ι → ℕ) (targetWeight : κ → ℕ),
    (∀ j, degree targetWeight (right j) = degree sourceWeight (left j)) →
    ∀ T : generated left →ₗ[ℤ] generated right,
      (∀ j, T (evaluateGenerators left (generator j)) =
        evaluateGenerators right (generator j)) →
      ∀ x : generated left,
        degree targetWeight (T x : IntegralLattice κ) =
          degree sourceWeight (x : IntegralLattice ι)

/-- Norm one in an integral orthonormal lattice gives a signed basis element.
The index is unique; the statement does not discard the negative sign. -/
def IntegralNormOneSignedBasisStatement (ι : Type u) : Prop :=
  ∀ x : IntegralLattice ι, pairing x x = 1 →
    ∃! i : ι, x = generator i ∨ x = -generator i

/-- Positive degree selects the positive sign. The weights are natural numbers;
zero weights are allowed, but cannot contribute a positive-degree norm-one vector. -/
def IntegralPositiveDegreeBasisStatement (ι : Type u) : Prop :=
  ∀ (weight : ι → ℕ) (x : IntegralLattice ι),
    pairing x x = 1 → 0 < degree weight x →
    ∃! i : ι, x = generator i

/-- An integral isometry is injective, independently of degree or surjectivity. -/
def IntegralIsometryInjectivityStatement (ι : Type u) (κ : Type v) : Prop :=
  ∀ T : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ,
    (∀ x y, pairing (T x) (T y) = pairing x y) →
    Function.Injective T

/-- An integral isometric embedding maps the basis injectively to signed
target basis elements. Surjectivity of the index map is not claimed. -/
def IntegralIsometrySignedBasisStatement (ι : Type u) (κ : Type v) : Prop :=
  ∀ T : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ,
    (∀ x y, pairing (T x) (T y) = pairing x y) →
    ∃ (f : ι → κ) (sign : ι → ℤ),
      Function.Injective f ∧
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      ∀ i, T (generator i) = sign i • generator (f i)

/-- A degree-preserving integral isometry with positive source-basis degrees
maps basis elements to positive target basis elements of the same degree. -/
def IntegralIsometryPositiveBasisStatement (ι : Type u) (κ : Type v) : Prop :=
  ∀ (sourceWeight : ι → ℕ) (targetWeight : κ → ℕ),
    (∀ i, 0 < sourceWeight i) →
    ∀ T : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ,
      (∀ x y, pairing (T x) (T y) = pairing x y) →
      (∀ x, degree targetWeight (T x) = degree sourceWeight x) →
      ∃ f : ι → κ,
        Function.Injective f ∧
        (∀ i, T (generator i) = generator (f i)) ∧
        ∀ i, targetWeight (f i) = sourceWeight i

/-- The elementary integral-lattice theorem family, before any local
representation-class instantiation or numerical surjectivity theorem. -/
def IntegralDescentAndPositivityStatement (ι : Type u) (κ : Type v) (J : Type w) : Prop :=
  IntegralPairingDefinitenessStatement ι ∧
  IntegralPairingDefinitenessStatement κ ∧
  IntegralRelationDescentStatement ι κ J ∧
  IntegralGeneratedEquivalenceStatement ι κ J ∧
  IntegralGeneratedIsometryStatement ι κ J ∧
  IntegralGeneratedDegreeStatement ι κ J ∧
  IntegralNormOneSignedBasisStatement ι ∧
  IntegralNormOneSignedBasisStatement κ ∧
  IntegralPositiveDegreeBasisStatement ι ∧
  IntegralPositiveDegreeBasisStatement κ ∧
  IntegralIsometryInjectivityStatement ι κ ∧
  IntegralIsometrySignedBasisStatement ι κ ∧
  IntegralIsometryPositiveBasisStatement ι κ

end Langlands.VirtualRepresentation
