import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasCanonicality
import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasComparisonProof

/-! # Independence and naturality of regular atlases: proof -/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

variable {k : Type} [RCLike k]
variable {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [IsAffine Y.left] {d e : ℕ}

namespace RegularAtlas

/-- Postcomposition with an actual relative morphism is real `C∞` from any regular atlas on the
source to any regular atlas on the target. -/
theorem contMDiff_postcomp (A : RegularAtlas k X d) (B : RegularAtlas k Y e) (f : X ⟶ Y) :
    @ContMDiff ℝ _ (Fin d → k) _ _ (Fin d → k) _ 𝓘(ℝ, Fin d → k)
      (RingPoint k X k) _ A.chartedSpace
      (Fin e → k) _ _ (Fin e → k) _ 𝓘(ℝ, Fin e → k)
      (RingPoint k Y k) _ B.chartedSpace ∞ (fun p => p ≫ f) := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  have hid : RegularSmooth 𝓘(ℝ, Fin d → k) (fun p : RingPoint k X k => p) :=
    fun a => A.contMDiff_regularEvaluation a
  exact (B.contMDiff_iff_regularSmooth 𝓘(ℝ, Fin d → k) (fun p : RingPoint k X k => p ≫ f)).2
    (hid.postcomp f)

/-- An actual relative isomorphism gives a real `C∞` diffeomorphism between any two regular
atlases, with the actual postcomposition maps in both directions. -/
def postcompDiffeomorph (A : RegularAtlas k X d) (B : RegularAtlas k Y e) (f : X ≅ Y) :
    @Diffeomorph ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
      (Fin d → k) _ (Fin e → k) _
      𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
      (RingPoint k X k) _ A.chartedSpace (RingPoint k Y k) _ B.chartedSpace ∞ :=
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  let _ : ChartedSpace (Fin e → k) (RingPoint k Y k) := B.chartedSpace
  { toFun p := p ≫ f.hom
    invFun q := q ≫ f.inv
    left_inv p := (Category.assoc p f.hom f.inv).trans
      ((congrArg (p ≫ ·) f.hom_inv_id).trans (Category.comp_id p))
    right_inv q := (Category.assoc q f.inv f.hom).trans
      ((congrArg (q ≫ ·) f.inv_hom_id).trans (Category.comp_id q))
    contMDiff_toFun := A.contMDiff_postcomp B f.hom
    contMDiff_invFun := B.contMDiff_postcomp A f.inv }

end RegularAtlas

/-- Identity diffeomorphisms between regular atlases, smoothness of actual morphisms and of
regular evaluations, and diffeomorphisms from actual isomorphisms. -/
theorem regularAtlasCanonicality (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularAtlasCanonicalityStatement k X d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e A B
    refine ⟨A.postcompDiffeomorph B (Iso.refl X), ?_⟩
    intro eF
    exact Equiv.ext fun p => Category.comp_id p
  · intro Y _ e A B f
    exact A.contMDiff_postcomp B f
  · intro A a
    exact A.contMDiff_regularEvaluation a
  · intro Y _ e A B f
    exact ⟨A.postcompDiffeomorph B f, fun _ => rfl, fun _ => rfl⟩

end Langlands.AlgebraicGeometry.PointManifold
