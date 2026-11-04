import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Lie.ActionDeterminant
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # A vector filtration of a rational dynamic unipotent subgroup with adjoint determinant -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Over a nonarchimedean local field `k`, let `χ` be a cocharacter of a connected reductive
group `G` and `m` a rational point of the centralizer `Z(χ)`, with image `g` in `G(k)`. Then
the closed subgroup `U(χ)(k)` of `G(k)` has a finite chain of subgroups
`U(χ)(k) = F 0 ⊇ F 1 ⊇ ⋯ ⊇ F N = 1`, each normalized by `g`, together with continuous, open,
surjective homomorphisms `q r : F r → k^(n r)` with kernel `F (r + 1)` and `k`-linear
automorphisms `L r` of `k^(n r)` satisfying `q r (g x g⁻¹) = L r (q r x)`, such that the product
of the determinants of the `L r` is `det(Ad m | Lie U(χ))`. This is a proof target. -/
def DynamicUnipotentVectorFiltrationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
      (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
      (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (m : rationalPoints Z),
      ∃ (N : ℕ) (F : ℕ → Subgroup (RationalPoint k G.X)) (n : ℕ → ℕ)
        (q : ∀ r, F r → Fin (n r) → k)
        (L : ∀ r, (Fin (n r) → k) ≃ₗ[k] (Fin (n r) → k)),
        F 0 = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) ∧ F N = ⊥ ∧
        (∀ r < N, F (r + 1) ≤ F r) ∧
        (∀ r < N, (m ≫ iZ.hom.hom : RationalPoint k G.X) ∈
          Subgroup.normalizer (F r : Set (RationalPoint k G.X))) ∧
        (∀ r < N, ∀ x y : F r, q r (x * y) = q r x + q r y) ∧
        (∀ r < N, ∀ x : F r, q r x = 0 ↔ (x : RationalPoint k G.X) ∈ F (r + 1)) ∧
        (∀ r < N, Continuous (q r)) ∧
        (∀ r < N, IsOpenMap (q r)) ∧
        (∀ r < N, Function.Surjective (q r)) ∧
        (∀ r < N, ∀ x y : F r, (y : RationalPoint k G.X) =
          (m ≫ iZ.hom.hom : RationalPoint k G.X) * x *
            (m ≫ iZ.hom.hom : RationalPoint k G.X)⁻¹ →
          q r y = L r (q r x)) ∧
        ∏ r ∈ Finset.range N, LinearEquiv.det (L r) =
          rationalCharacterEval
            ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m

end Langlands.Aubert.General.RationalPointFamily
