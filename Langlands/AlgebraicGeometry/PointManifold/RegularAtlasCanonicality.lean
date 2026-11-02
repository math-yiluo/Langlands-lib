import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasComparison
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Independence and naturality of regular atlases: exact targets -/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

variable (k : Type) [RCLike k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ)

/-- The identity is a diffeomorphism for any two regular atlases on the same
actual point space. Both charted-space arguments are explicit. -/
def regularAtlasIndependenceStatement : Prop :=
  ∀ (e : ℕ) (A : RegularAtlas k X d) (B : RegularAtlas k X e),
    ∃ F : @Diffeomorph ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ A.chartedSpace (RingPoint k X k) _ B.chartedSpace ∞,
      let eF := @Diffeomorph.toEquiv ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ A.chartedSpace (RingPoint k X k) _ B.chartedSpace ∞ F
      eF = Equiv.refl (RingPoint k X k)

/-- Actual algebraic morphisms induce smooth maps for every pair of regular
atlases, allowing different source and target dimensions. -/
def regularAtlasMorphismSmoothnessStatement : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of k))) [IsAffine Y.left]
    (e : ℕ) (A : RegularAtlas k X d) (B : RegularAtlas k Y e) (f : X ⟶ Y),
    @ContMDiff ℝ _ (Fin d → k) _ _ (Fin d → k) _ 𝓘(ℝ, Fin d → k)
      (RingPoint k X k) _ A.chartedSpace
      (Fin e → k) _ _ (Fin e → k) _ 𝓘(ℝ, Fin e → k)
      (RingPoint k Y k) _ B.chartedSpace ∞ (fun p => p ≫ f)

/-- Every global regular-function evaluation is smooth on every regular atlas. -/
def regularAtlasEvaluationSmoothnessStatement : Prop :=
  ∀ A : RegularAtlas k X d,
    letI := A.chartedSpace
    ∀ a : AffineCoordinateRing k X,
      ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, k) ∞
        (fun p : RingPoint k X k => regularEvaluation p a)

/-- Changing the affine scheme presentation by an actual isomorphism gives a
point diffeomorphism with the actual postcomposition maps in both directions. -/
def regularAtlasIsomorphismStatement : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of k))) [IsAffine Y.left]
    (e : ℕ) (A : RegularAtlas k X d) (B : RegularAtlas k Y e) (f : X ≅ Y),
    ∃ F : @Diffeomorph ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ A.chartedSpace (RingPoint k Y k) _ B.chartedSpace ∞,
      let eF := @Diffeomorph.toEquiv ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ A.chartedSpace (RingPoint k Y k) _ B.chartedSpace ∞ F
      (∀ p, eF p = p ≫ f.hom) ∧ (∀ q, eF.symm q = q ≫ f.inv)

/-- The choice independence and actual-map consequences of the intrinsic family
criterion, separate from the algebraic chart-existence obligation. -/
def regularAtlasCanonicalityStatement : Prop :=
  regularAtlasIndependenceStatement k X d ∧
    regularAtlasMorphismSmoothnessStatement k X d ∧
    regularAtlasEvaluationSmoothnessStatement k X d ∧
    regularAtlasIsomorphismStatement k X d

end Langlands.AlgebraicGeometry.PointManifold
