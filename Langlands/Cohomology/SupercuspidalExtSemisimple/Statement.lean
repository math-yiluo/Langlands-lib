import Langlands.Cohomology.SupercuspidalExtCharZero.Statement
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Supercuspidal Ext vanishing over a semisimple commutative ℚ-algebra

Harris (1999) takes `Ext` in the category of smooth `L_ℓ[GJ]`-modules, where
`L_ℓ = L ⊗_ℚ ℚ_ℓ` for a number field `L`. This ring is a finite product of
fields of characteristic zero. The module replaces the coefficient field of
the published characteristic-zero statements by a commutative semisimple
`ℚ`-algebra `A`. Irreducibility means that the lattice of subrepresentations is
simple, and matrix coefficients are taken against `A`-linear dual vectors.
None of the assertions is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Cohomology.SupercuspidalExtSemisimple

open Langlands.Cohomology.SupercuspidalExt (restriction compactInduction)

universe u

/-- A smooth representation over a commutative ring is irreducible if its
lattice of subrepresentations is simple: it is nonzero, and its only
subrepresentations are `0` and itself. Over a field this is
`SmoothRep.IsIrreducible`. -/
def IsIrreducible {A : Type u} [CommRing A] {G : Type u} [Group G] [TopologicalSpace G]
    (ρ : SmoothRep.{u, u, u} A G) : Prop :=
  IsSimpleOrder (Subrepresentation ρ.representation)

/-- A smooth representation over a commutative ring whose matrix coefficients
against smooth `A`-linear dual vectors all have compact support. -/
def HasCompactCoefficients {A : Type u} [CommRing A] {G : Type u} [Group G]
    [TopologicalSpace G] (ρ : SmoothRep.{u, u, u} A G) : Prop :=
  ∀ (v : ρ) (ℓ : Module.Dual A ρ), IsSmoothVector ρ.representation.dual ℓ →
    HasCompactSupport (matrixCoefficient ρ.representation ℓ v)

/-- Over a commutative semisimple `ℚ`-algebra `A`, an irreducible smooth
representation with compactly supported matrix coefficients is an injective
and a projective object of the category of smooth `A`-representations. The
group is locally profinite, σ-compact and unimodular. -/
def CompactCoefficientInjectiveProjectiveStatement
    (A : Type u) [CommRing A] [IsSemisimpleRing A] [Algebra ℚ A]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  ∀ ρ : SmoothRep.{u, u, u} A G, IsIrreducible ρ →
    HasCompactCoefficients ρ → Injective ρ ∧ Projective ρ

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Over a commutative semisimple `ℚ`-algebra `A`: let `G₀` be an open
subgroup and `π` a smooth representation of `G` whose restriction to `G₀` is a
finite direct sum of irreducible representations with compactly supported
matrix coefficients on `G₀`. Then `Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0` for
every smooth representation `V` of `G₀` and every `n`. -/
def CompactInductionSupercuspidalExtVanishingStatement
    (A : Type u) [CommRing A] [IsSemisimpleRing A] [Algebra ℚ A]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  ∀ (G₀ : Subgroup G), IsOpen (G₀ : Set G) →
    ∀ (π : SmoothRep.{u, u, u} A G) (ι : Type) [Finite ι]
      (σ : ι → SmoothRep.{u, u, u} A G₀),
      (∀ i, IsIrreducible (σ i)) → (∀ i, HasCompactCoefficients (σ i)) →
      Nonempty ((restriction A G G₀).obj π ≅ ⨁ σ) →
      ∀ (V : SmoothRep.{u, u, u} A G₀) (n : ℕ),
        IsZero ((SmoothExt.ext A G ((compactInduction A G G₀).obj V) (n + 1)).obj π)

/-- The supercuspidal `Ext` statements over a commutative semisimple
`ℚ`-algebra: the published `Ext` reciprocity for compact induction, taken over
`A`, and the two propositions above. None of the three is assumed to be
true. -/
def SupercuspidalExtSemisimpleStatements
    (A : Type u) [CommRing A] [IsSemisimpleRing A] [Algebra ℚ A]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  SupercuspidalExt.CompactInductionExtReciprocityStatement A G ∧
  CompactCoefficientInjectiveProjectiveStatement A G μ ∧
  CompactInductionSupercuspidalExtVanishingStatement A G μ

/-- Over a field of characteristic zero, irreducibility in this module is
`SmoothRep.IsIrreducible`. -/
theorem isIrreducible_field_iff {k : Type u} [Field k] {G : Type u} [Group G]
    [TopologicalSpace G] (ρ : SmoothRep.{u, u, u} k G) :
    IsIrreducible ρ ↔ ρ.IsIrreducible :=
  Iff.rfl

/-- Over a field, compactness of matrix coefficients in this module is the
published predicate of the characteristic-zero statements. -/
theorem hasCompactCoefficients_field_iff {k : Type u} [Field k] {G : Type u} [Group G]
    [TopologicalSpace G] (ρ : SmoothRep.{u, u, u} k G) :
    HasCompactCoefficients ρ ↔ SupercuspidalExtCharZero.HasCompactCoefficients ρ :=
  Iff.rfl

/-- At a field of characteristic zero, with its canonical `ℚ`-algebra
structure, the statements specialize to the published characteristic-zero
ones. -/
theorem supercuspidalExtCharZeroStatements_of_semisimple
    (k : Type u) [Field k] [CharZero k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] :
    SupercuspidalExtSemisimpleStatements k G μ →
      SupercuspidalExtCharZero.SupercuspidalExtCharZeroStatements k G μ :=
  id

end Langlands.Cohomology.SupercuspidalExtSemisimple
