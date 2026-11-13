import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Examples.SU3GroupScheme
import Langlands.GroupScheme.SpecialLinearWeilPointModels
import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.Torus.LatticeGalois

/-!
# An all-test Hermitian matrix presentation of outer type-A groups

This module states that a simply connected absolutely almost-simple group whose
actual Cartan pairings are numbered as type `A_n`, whose full star action is the
reversal of the chain, and whose two end vertices are distinguished, is the special
unitary group of a nonsingular Hermitian matrix over a separable quadratic extension,
presented on every test scheme by actual matrices over the tensor coefficient ring,
with the maximal split torus acting diagonally through explicit characters. The
statement is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If the actual Cartan pairings are of type `A_n` under `e`, the full star image is
`{1, reversal}`, and both end vertices are distinguished, then there are a separable
quadratic extension `L/K`, a nonsingular Hermitian matrix `J` over `L`, injective group
homomorphisms `ρ T` from the points of `G` over every test scheme `T` to
`GL_(n+1)(L ⊗_K Γ(T))` with image exactly the determinant-one isometries of `J`,
natural in `T`, and characters `χ i` of the maximal split torus such that `ρ` sends a
split-torus point `s` to the diagonal matrix with entries `χ i (s)`, and the
restriction of the simple root numbered `i` is `χ i - χ (i + 1)`. -/
def OuterTypeAHermitianPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
    d.StarImagePair e Fin.revPerm →
    (∀ a, ((e a).val = 0 ∨ (e a).val + 1 = n) → a ∈ d.distinguishedVertices) →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L)
      (ι₀ : L →ₐ[K] SeparableClosure K)
      (J : Matrix (Fin (n + 1)) (Fin (n + 1)) L)
      (ρ : ∀ T : Over (Spec (CommRingCat.of K)),
        (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin (n + 1))
          (SpecialLinear.WeilRoot.tensorAlgebra K L T))
      (χ : Fin (n + 1) → characterLattice d.splitTorus),
      (∀ τ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
        (∀ y, τ (ι₀ y) = ι₀ y) ↔ ∀ v, d.star τ v = v) ∧
      (J.map (SU3Root.fieldInvolution K L).bar).transpose = J ∧ IsUnit J.det ∧
      (∀ T, Function.Injective (ρ T)) ∧
      (∀ (T : Over (Spec (CommRingCat.of K)))
          (g : Matrix.GeneralLinearGroup (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)),
        g ∈ (ρ T).range ↔
          (((g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
              J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
              (g : Matrix (Fin (n + 1)) (Fin (n + 1))
                (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
            J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
          Matrix.GeneralLinearGroup.det g = 1)) ∧
      (∀ {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) (x : T ⟶ G.X),
        (ρ T' (a ≫ x) : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
          (ρ T x : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
              (SpecialLinear.WeilRoot.tensorMap K L a)) ∧
      (∀ (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ d.splitTorus.X),
        (ρ T (s ≫ d.splitInclusion.hom.hom) : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
          Matrix.diagonal fun i =>
            (show SpecialLinear.WeilRoot.tensorAlgebra K L T from
              Algebra.TensorProduct.includeRight (R := K) (A := L)
                (B := SpecialLinear.WeilRoot.sectionAlgebra K T)
                (show SpecialLinear.WeilRoot.sectionAlgebra K T from
                  ((Gm.pointsEquiv _ T (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
                    Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))))) ∧
      ∀ i : Fin n, d.rootRestriction (e.symm i).val = χ i.castSucc - χ i.succ

end Langlands.GroupScheme
