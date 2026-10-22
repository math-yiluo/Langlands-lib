import Langlands.Cohomology.SupercuspidalExt.Statement

/-!
# Supercuspidal Ext vanishing over a field of characteristic zero

The coefficient field of the published complex supercuspidal `Ext` statements
is replaced by an arbitrary field of characteristic zero, such as a finite
extension of `ℚ_ℓ` or an algebraic closure of `ℚ_ℓ`. The module defines
compactness of matrix coefficients over such a field and two propositions:
injectivity and projectivity of an irreducible smooth representation with
compactly supported matrix coefficients, and the resulting vanishing of
higher `Ext` from a compactly induced representation. None of the assertions
is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open Langlands.Cohomology.SupercuspidalExt (restriction compactInduction)

universe u

/-- A smooth representation over a field `k` whose matrix coefficients against
smooth dual vectors all have compact support. -/
def HasCompactCoefficients {k : Type u} [Field k] {G : Type u} [Group G]
    [TopologicalSpace G] (ρ : SmoothRep.{u, u, u} k G) : Prop :=
  ∀ (v : ρ) (ℓ : Module.Dual k ρ), IsSmoothVector ρ.representation.dual ℓ →
    HasCompactSupport (matrixCoefficient ρ.representation ℓ v)

/-- Over `ℂ`, for a group in `Type`, this is the published complex predicate. -/
theorem hasCompactCoefficients_complex_iff {G : Type} [Group G] [TopologicalSpace G]
    (ρ : SmoothRep.{0, 0, 0} ℂ G) :
    HasCompactCoefficients ρ ↔ SupercuspidalExt.HasCompactCoefficients ρ :=
  Iff.rfl

/-- Over a field of characteristic zero, an irreducible smooth representation
with compactly supported matrix coefficients is an injective and a projective
object of the category of smooth representations. The group is locally
profinite, σ-compact and unimodular. -/
def CompactCoefficientInjectiveProjectiveStatement
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  ∀ ρ : SmoothRep.{u, u, u} k G, ρ.IsIrreducible →
    HasCompactCoefficients ρ → Injective ρ ∧ Projective ρ

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Over a field of characteristic zero: let `G₀` be an open subgroup and `π` a
smooth representation of `G` whose restriction to `G₀` is a finite direct sum
of irreducible representations with compactly supported matrix coefficients
on `G₀`. Then `Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0` for every smooth
representation `V` of `G₀` and every `n`. -/
def CompactInductionSupercuspidalExtVanishingStatement
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  ∀ (G₀ : Subgroup G), IsOpen (G₀ : Set G) →
    ∀ (π : SmoothRep.{u, u, u} k G) (ι : Type) [Finite ι]
      (σ : ι → SmoothRep.{u, u, u} k G₀),
      (∀ i, (σ i).IsIrreducible) → (∀ i, HasCompactCoefficients (σ i)) →
      Nonempty ((restriction k G G₀).obj π ≅ ⨁ σ) →
      ∀ (V : SmoothRep.{u, u, u} k G₀) (n : ℕ),
        IsZero ((SmoothExt.ext k G ((compactInduction k G G₀).obj V) (n + 1)).obj π)

/-- The supercuspidal `Ext` statements over a field of characteristic zero:
the published `Ext` reciprocity for compact induction, taken over `k`, and the
two propositions above. None of the three is assumed to be true. -/
def SupercuspidalExtCharZeroStatements
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  SupercuspidalExt.CompactInductionExtReciprocityStatement k G ∧
  CompactCoefficientInjectiveProjectiveStatement k G μ ∧
  CompactInductionSupercuspidalExtVanishingStatement k G μ

/-- At `k = ℂ` and a group in `Type`, the statements specialize to the published
complex ones. -/
theorem supercuspidalExtStatements_of_charZero
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] :
    SupercuspidalExtCharZeroStatements ℂ G μ →
      SupercuspidalExt.SupercuspidalExtStatements G μ :=
  id

end Langlands.Cohomology.SupercuspidalExtCharZero
