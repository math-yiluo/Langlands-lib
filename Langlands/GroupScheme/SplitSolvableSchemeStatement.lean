import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.Split
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # The underlying scheme of a split solvable group (Milne 16.56) -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.56 (first sentence): let `G` be a split solvable group over a
field `k`, with canonical extension `e → U → G → D → e` (`U = G_u` a normal unipotent closed
subgroup, `q : G ⟶ D` an fppf quotient by it onto a group of multiplicative type). Then for some
`r` and `m`, `U` is isomorphic as a `k`-scheme to `𝔸^r`, `D` is the split torus `G_m^m`, and the
underlying scheme of `G` is isomorphic over `k` to `𝔸^r × G_m^m`. -/
def SplitSolvableSchemeProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSplitSolvableGroupScheme G →
    ∀ (U D : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (q : G ⟶ D),
      IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q → IsMultiplicativeType D →
      ∃ r m : ℕ,
        Nonempty (U.X ≅ Over.mk (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of k)) ↘
          Spec (CommRingCat.of k))) ∧
        Nonempty (D ≅ splitTorus (Spec (CommRingCat.of k)) (ULift.{u} (Fin m))) ∧
        Nonempty (G.X ≅ Over.mk (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of k)) ↘
          Spec (CommRingCat.of k)) ⊗ (splitTorus (Spec (CommRingCat.of k)) (ULift.{u} (Fin m))).X)

end Langlands.GroupScheme
