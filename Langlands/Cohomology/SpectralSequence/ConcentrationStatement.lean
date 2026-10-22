import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
Proposition targets for comparison and concentration of actual cohomological
spectral sequences. These declarations do not assert theorem proofs.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u v

/-- Isomorphisms on the second page of a morphism of spectral sequences
propagate to every subsequent finite page. -/
def SpectralSequenceComparisonStatement (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  ∀ (E E' : CohomologicalSpectralSequence C 2) (f : E ⟶ E'),
    (∀ pq : ℤ × ℤ, IsIso ((f.hom 2).f pq)) →
    ∀ (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ), IsIso ((f.hom r hr).f pq)

/-- A spectral sequence supported on one column on its second page has zero
differentials and the same objects up to isomorphism on every later page. -/
def SingleColumnDegenerationStatement (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  ∀ (E : CohomologicalSpectralSequence C 2) (p₀ : ℤ),
    (∀ pq : ℤ × ℤ, pq.1 ≠ p₀ → IsZero ((E.page 2).X pq)) →
    ∀ (r : ℤ) (hr : 2 ≤ r),
      (∀ pq : ℤ × ℤ, pq.1 ≠ p₀ → IsZero ((E.page r hr).X pq)) ∧
      (∀ pq pq' : ℤ × ℤ, (E.page r hr).d pq pq' = 0) ∧
      (∀ pq : ℤ × ℤ, Nonempty ((E.page 2).X pq ≅ (E.page r hr).X pq))

/-- A spectral sequence supported on one row on its second page has zero
differentials and the same objects up to isomorphism on every later page. -/
def SingleRowDegenerationStatement (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  ∀ (E : CohomologicalSpectralSequence C 2) (q₀ : ℤ),
    (∀ pq : ℤ × ℤ, pq.2 ≠ q₀ → IsZero ((E.page 2).X pq)) →
    ∀ (r : ℤ) (hr : 2 ≤ r),
      (∀ pq : ℤ × ℤ, pq.2 ≠ q₀ → IsZero ((E.page r hr).X pq)) ∧
      (∀ pq pq' : ℤ × ℤ, (E.page r hr).d pq pq' = 0) ∧
      (∀ pq : ℤ × ℤ, Nonempty ((E.page 2).X pq ≅ (E.page r hr).X pq))

/-- Concentration in one bidegree is preserved, with zero differentials,
on every later finite page. This does not postulate an abutment. -/
def SinglePositionDegenerationStatement (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  ∀ (E : CohomologicalSpectralSequence C 2) (pq₀ : ℤ × ℤ),
    (∀ pq : ℤ × ℤ, pq ≠ pq₀ → IsZero ((E.page 2).X pq)) →
    ∀ (r : ℤ) (hr : 2 ≤ r),
      (∀ pq : ℤ × ℤ, pq ≠ pq₀ → IsZero ((E.page r hr).X pq)) ∧
      (∀ pq pq' : ℤ × ℤ, (E.page r hr).d pq pq' = 0) ∧
      Nonempty ((E.page 2).X pq₀ ≅ (E.page r hr).X pq₀)

/-- The comparison and concentration prerequisites for spectral-sequence
arguments. None of these four propositions is assumed to be true. -/
def SpectralSequenceConcentrationStatements (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  SpectralSequenceComparisonStatement C ∧
  SingleColumnDegenerationStatement C ∧
  SingleRowDegenerationStatement C ∧
  SinglePositionDegenerationStatement C

end Langlands.Cohomology
