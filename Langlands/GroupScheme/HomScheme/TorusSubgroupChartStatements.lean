import Langlands.GroupScheme.HomScheme.TorusSubgroupCharts
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityStatement

/-! # Chart covers of the functor of closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- Every smooth affine group scheme over an arbitrary base has a family of open
charts of its closed torus subgroup functor covering all field points. -/
def ChartCoverStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ∃ (ι : Type u) (U : ι → Over S) (K : ∀ k, GroupScheme (U k).left)
      (j : ∀ k, K k ⟶ (GroupScheme.baseChange (U k).hom).obj G),
      (∀ k, IsOpenChart (j k)) ∧ CoversFieldPoints j

/-- The chart-cover property over affine bases of finite type over `ℤ`. -/
def FiniteTypeChartCoverStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ∃ (ι : Type u) (U : ι → Over (Spec (CommRingCat.of R)))
      (K : ∀ k, GroupScheme (U k).left)
      (j : ∀ k, K k ⟶ (GroupScheme.baseChange (U k).hom).obj G),
      (∀ k, IsOpenChart (j k)) ∧ CoversFieldPoints j

/-- Gluing: a chart cover of every smooth affine group scheme yields the smooth
moduli scheme of actual closed torus subgroups. -/
def ChartGluingStatement : Prop :=
  ChartCoverStatement.{u} → SmoothTorusSubgroupRepresentabilityStatement.{u}

/-- Noetherian reduction: chart covers over affine bases of finite type over
`ℤ` yield chart covers over every base. -/
def ChartCoverReductionStatement : Prop :=
  FiniteTypeChartCoverStatement.{u} → ChartCoverStatement.{u}

end Langlands.GroupScheme.TorusSubgroupModuli
