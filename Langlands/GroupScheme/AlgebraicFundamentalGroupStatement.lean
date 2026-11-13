import Langlands.GroupScheme.AlgebraicFundamentalGroup
import Mathlib.FieldTheory.IsSepClosed

/-! # KP Construction 11.3.1: structure and canonical comparisons -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

/-- The preimage is maximal, its cocharacter map is injective, and its quotient
is finitely generated. These are unconditional obligations of Construction 11.3.1. -/
def AlgebraicFundamentalGroupStructureStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive G)
    (a : Choice k G),
    IsMaximalTorus a.scInclusion ∧
    Function.Injective (a.corootMap E) ∧ Module.Finite ℤ (a.atChoice E)

/-- Canonical, Galois-equivariant and coherent comparison between every two
presentations, independent of every geometric conjugator. -/
def AlgebraicFundamentalGroupComparisonStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive G),
    (∀ a b : Choice k G,
      (∃! f, a.IsCanonicalComparison E b f) ∧
      a.IsCanonicalComparison E b (a.comparison E b) ∧
      Function.Bijective (a.comparison E b) ∧
      (∀ (σ : E ≃ₐ[k] E) (x : a.atChoice E),
        a.comparison E b (a.galoisRepresentation E σ x) =
          b.galoisRepresentation E σ (a.comparison E b x)) ∧
      (∀ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
        (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
          (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
        a.IsConjugationComparison E b g e →
        ∀ ν : a.lattice E,
          a.comparison E b (a.projection E ν) = b.projection E (ν ≫ e.hom))) ∧
    (∀ a : Choice k G, a.comparison E a = LinearMap.id) ∧
    (∀ a b c : Choice k G,
      (b.comparison E c).comp (a.comparison E b) = a.comparison E c)

end Langlands.GroupScheme.AlgebraicFundamentalGroup
