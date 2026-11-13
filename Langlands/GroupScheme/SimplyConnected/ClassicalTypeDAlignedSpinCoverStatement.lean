import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeight

/-!
# Spin covers aligned with a numbered type-D diagram

This unproved prerequisite states the classical type-`D` realization over an
arbitrary field: a simply connected group with a numbered type-`D` diagram whose
star action fixes the nonfork vertices is a spin cover of the orthogonal group
of a nondegenerate quadratic form over a central division algebra, with the
vector vertex at the vertex numbered `0`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A simply connected absolutely almost-simple group with a numbered
type-`D_n` index (`n ≥ 4`) whose full star action fixes the nonfork vertices has
a spin cover `π : G ⟶ O(q)` of a nondegenerate `σ`-quadratic form `q` on `D^m`,
where `D` is central division of degree `degree`, `m * degree = 2 * n` and `σ`
has Tits type 1, such that the fundamental weight at the vertex numbered `0` is
trivial on `ker π` in the pinning torus over `K^s`.

This is an unproved general classification prerequisite. There is no rank-one,
local-field or characteristic hypothesis. -/
def ClassicalTypeDAlignedSpinCoverStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n →
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    (∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a) →
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D)
      (degree m : ℕ),
      0 < degree ∧ Module.finrank K D = degree ^ 2 ∧ m * degree = 2 * n ∧
        ∃ σ : Quaternionic.FirstKindInvolution K D,
          Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
            ∃ q : σ.QuadraticForms (Fin m),
              σ.IsNondegenerateQuadratic q ∧
                ∃ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π ∧
                  ∀ v : d.Vertex, (e v).val = 0 → d.FundamentalWeightTrivialOnKernel v π

end Langlands.GroupScheme
