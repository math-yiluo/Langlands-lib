import Langlands.GroupScheme.SimplyConnected.OuterTypeARankOneHermitianStatement
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationStatement
import Langlands.GroupScheme.Rational.HermitianMatrixSplitRankStatement
import Langlands.GroupScheme.Examples.HermitianMatrixNondegenerate
import Langlands.GroupScheme.Examples.HermitianRankOneModel

/-! # Reduction of the rank-one outer-A model to presentation and split rank -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The general outer-A matrix presentation and the actual Hermitian split-rank
comparison together imply the exact rank-one Hermitian model statement. -/
theorem outerTypeARankOneHermitian_of_presentation_and_splitRank
    (hp : OuterTypeAHermitianPresentationStatement.{u})
    (hr : HermitianMatrixSplitRankStatement.{u}) :
    OuterTypeARankOneHermitianStatement.{u} := by
  intro K _ G _ _ d n hsc haas hindex hsplit
  obtain ⟨hn, e, hnumbering, hstar⟩ := hindex
  have hn2 : 2 ≤ n := by omega
  obtain ⟨L, fieldL, algKL, quadraticKL, separableKL, _embedding, J, ρ, _χ,
      _hkernel, hJ, hdet, hinj, hrange, hnat, _htorus, _hroots⟩ :=
    hp K G d n e hsc haas hnumbering.1 hstar
      (fun a ha => (hnumbering.2 a).mpr ha)
  let : Field L := fieldL
  let : Algebra K L := algKL
  let : Algebra.IsQuadraticExtension K L := quadraticKL
  let : Algebra.IsSeparable K L := separableKL
  let J₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) L :=
    Matrix.GeneralLinearGroup.mk'' J hdet
  let F : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin (n + 1)) :=
    ⟨J₀, hJ⟩
  have hrange' (T : Over (Spec (CommRingCat.of K)))
      (g : Matrix.GeneralLinearGroup (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L T)) :
      (∃ x : T ⟶ G.X, ρ T x = g) ↔
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1))
            (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
            J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
            (g : Matrix (Fin (n + 1)) (Fin (n + 1))
              (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
          J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
          Matrix.GeneralLinearGroup.det g = 1 :=
    hrange T g
  obtain ⟨⟨W, hW, hdim⟩, hmax⟩ := hr K L n hn2 G J₀ hJ ρ hinj hrange' hnat
  have hatt : ∃ W : Submodule L (Fin (n + 1) → L),
      (∀ a b : W, F.linearFirst (a : Fin (n + 1) → L)
        (b : Fin (n + 1) → L) = 0) ∧ (Module.finrank L W : ℕ∞) = 1 := by
    refine ⟨W, ?_, hdim.trans hsplit⟩
    intro a b
    exact (F.linearFirst_eq_dotProduct a.val b.val).trans (hW a b)
  have hbound (W : Submodule L (Fin (n + 1) → L))
      (hW : ∀ a b : W, F.linearFirst (a : Fin (n + 1) → L)
        (b : Fin (n + 1) → L) = 0) : (Module.finrank L W : ℕ∞) ≤ 1 := by
    rw [← hsplit]
    apply hmax W
    intro a b
    exact (F.linearFirst_eq_dotProduct a.val b.val).symm.trans (hW a b)
  obtain ⟨H, w, hw, hH, iso⟩ :=
    HermitianRoot.SchemeModel.rankOneModelOfAttainedPresentation K L
      (show 1 ≤ n by omega) (Fintype.card_fin (n + 1))
      F.linearFirst F.bar_linearFirst J F.linearFirst_eq_dotProduct
      F.linearFirst_nondegenerate hatt hbound ρ hinj hrange' hnat
  exact ⟨L, fieldL, algKL, quadraticKL, separableKL, H, w, hw, hH, ⟨iso⟩⟩

/-- Actual quadratic-extension and anisotropic-middle model data. -/
def OuterTypeARankOneHermitianModel (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ) :=
  Σ' (L : Type u) (_ : Field L) (_ : Algebra K L)
    (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L),
    HermitianRoot.SchemeModel.RankOneModel K L n G

/-- Choose actual model data using the two general presentation and rank
propositions, without treating either proposition as proved. -/
def outerTypeARankOneHermitianModelOfPresentationAndSplitRank
    (hp : OuterTypeAHermitianPresentationStatement.{u})
    (hr : HermitianMatrixSplitRankStatement.{u})
    (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hindex : d.HasRankOneOuterAIndex n) (hsplit : splitRank G = 1) :
    OuterTypeARankOneHermitianModel K G n := by
  apply Classical.choice
  obtain ⟨L, fieldL, algKL, quadraticKL, separableKL, H, w, hw, hH, ⟨iso⟩⟩ :=
    outerTypeARankOneHermitian_of_presentation_and_splitRank hp hr
      K G d n hsc haas hindex hsplit
  exact ⟨⟨L, fieldL, algKL, quadraticKL, separableKL, H, w, hw, hH, iso⟩⟩

end Langlands.GroupScheme
