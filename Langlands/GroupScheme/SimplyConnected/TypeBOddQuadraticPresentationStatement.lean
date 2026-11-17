import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Quaternionic.NormOneIsometry
import Langlands.GroupScheme.Quaternionic.RadicalFreeQuadratic
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Odd quadratic presentations of simply connected type-B groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Classical in
/-- Every actual simply connected absolutely almost-simple group of type
`B_n`, `n ≥ 3`, has a central isogeny onto the actual determinant-one
isometry group of a regular scalar quadratic form in dimension `2*n+1`,
and its split rank is the Witt index of that form.

This general classification statement is unproved. It has no local-field,
rank-one, perfection or characteristic hypothesis. -/
def TypeBOddQuadraticPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n),
    3 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) →
      ∃ q : (Quaternionic.FirstKindInvolution.scalar K).QuadraticForms (Fin (2 * n + 1)),
        (Quaternionic.FirstKindInvolution.scalar K).IsRadicalFreeQuadratic q ∧
        Module.finrank K
            (LinearMap.ker
              ((Quaternionic.FirstKindInvolution.scalar K).polar q).vecMulLinear) =
          (if (2 : K) = 0 then 1 else 0) ∧
        ((Quaternionic.FirstKindInvolution.scalar K).quadraticWittIndex q : ℕ∞) =
          splitRank G ∧
        ∃ π : G ⟶ (Quaternionic.FirstKindInvolution.scalar K).normOneIsometryGroup q,
          IsCentralIsogeny π

section Local

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The general odd-quadratic presentation, if proved, excludes local
split rank one in every actual type `B_n` with `n ≥ 3`. -/
theorem localRankOneTypeB_false_of_oddQuadraticPresentation
    (hpresentation : TypeBOddQuadraticPresentationStatement.{u})
    (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n) (hn : 3 ≤ n)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hB : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b))
    (hrank : splitRank G = 1) : False := by
  obtain ⟨q, hq, _, hw, _⟩ := hpresentation K G d n e hn hsc has hB
  have hw1 : (Quaternionic.FirstKindInvolution.scalar K).quadraticWittIndex q = 1 := by
    rw [hrank] at hw
    exact_mod_cast hw
  exact Quaternionic.FirstKindInvolution.scalar_quadraticWittIndex_ne_one_of_seven_le
    hq (by simpa only [Fintype.card_fin] using (show 7 ≤ 2 * n + 1 by omega)) hw1

end Local

end Langlands.GroupScheme
