import Langlands.Cohomology.SmoothExt
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.CompactCoefficient.SplittingStatement
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# Supercuspidal Ext vanishing

Restriction and compact induction between smooth representations of a group
and of a subgroup, and three proposition definitions: `Ext` reciprocity for
compact induction from an open subgroup; injectivity and projectivity of an
irreducible smooth complex representation with compactly supported matrix
coefficients; and the resulting vanishing of higher `Ext` from a compactly
induced representation into a representation whose restriction splits into
such representations. None of the three assertions is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace Langlands.Cohomology.SupercuspidalExt

universe u

section Functors

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Restriction of smooth representations to a subgroup, with the subspace
topology. Smoothness is preserved because the inclusion is continuous. -/
def restriction (H : Subgroup G) : SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R H :=
  (smoothRepProperty R H).lift (SmoothRep.toRep ⋙ Rep.resFunctor H.subtype)
    (fun A => isSmooth_comp H.subtype continuous_subtype_val A.isSmooth)

/-- Compact induction from a subgroup, on smooth representations: the published
`Induction.compactInductionFunctor` applied to the underlying representation. -/
abbrev compactInduction (H : Subgroup G) : SmoothRep.{u, u, u} R H ⥤ SmoothRep.{u, u, u} R G :=
  SmoothRep.toRep ⋙ Induction.compactInductionFunctor H

end Functors

section Statements

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- For an open subgroup `H` and a smooth representation `V` of `H`, the
functors `Ext^n_G(c-Ind_H^G V, -)` and `Ext^n_H(V, -) ∘ restriction` are
naturally isomorphic for every `n`. -/
def CompactInductionExtReciprocityStatement : Prop :=
  ∀ (H : Subgroup G), IsOpen (H : Set G) →
    ∀ (V : SmoothRep.{u, u, u} R H) (n : ℕ),
      Nonempty (SmoothExt.ext R G ((compactInduction R G H).obj V) n ≅
        restriction R G H ⋙ SmoothExt.ext R H V n)

end Statements

/-- A smooth complex representation whose matrix coefficients against smooth
dual vectors all have compact support. -/
def HasCompactCoefficients {G : Type u} [Group G] [TopologicalSpace G]
    (ρ : SmoothRep.{0, u, u} ℂ G) : Prop :=
  ∀ (v : ρ) (ℓ : Module.Dual ℂ ρ), IsSmoothVector ρ.representation.dual ℓ →
    HasCompactSupport (matrixCoefficient ρ.representation ℓ v)

/-- An irreducible smooth complex representation with compactly supported
matrix coefficients is an injective and a projective object of the category of
smooth complex representations. The group satisfies the hypotheses of
Bernstein–Zelevinsky 2.42, with a regular two-sided Haar measure. -/
def CompactCoefficientInjectiveProjectiveStatement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  ∀ ρ : SmoothRep.{0, 0, 0} ℂ G, ρ.representation.IsIrreducible →
    HasCompactCoefficients ρ → Injective ρ ∧ Projective ρ

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Let `G₀` be an open subgroup and `π` a smooth complex representation of `G`
whose restriction to `G₀` is a finite direct sum of irreducible
representations with compactly supported matrix coefficients on `G₀`. Then
`Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0` for every smooth representation `V` of
`G₀` and every `n`. -/
def CompactInductionSupercuspidalExtVanishingStatement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  ∀ (G₀ : Subgroup G), IsOpen (G₀ : Set G) →
    ∀ (π : SmoothRep.{0, 0, 0} ℂ G) (ι : Type) [Finite ι] (σ : ι → SmoothRep.{0, 0, 0} ℂ G₀),
      (∀ i, (σ i).representation.IsIrreducible) → (∀ i, HasCompactCoefficients (σ i)) →
      Nonempty ((restriction ℂ G G₀).obj π ≅ ⨁ σ) →
      ∀ (V : SmoothRep.{0, 0, 0} ℂ G₀) (n : ℕ),
        IsZero ((SmoothExt.ext ℂ G ((compactInduction ℂ G G₀).obj V) (n + 1)).obj π)

/-- The supercuspidal `Ext` statements used by Harris (1997, p.96) and Harris
(1999, p.312). None of the three is assumed to be true. -/
def SupercuspidalExtStatements
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] : Prop :=
  CompactInductionExtReciprocityStatement ℂ G ∧
  CompactCoefficientInjectiveProjectiveStatement G μ ∧
  CompactInductionSupercuspidalExtVanishingStatement G μ

end Langlands.Cohomology.SupercuspidalExt
