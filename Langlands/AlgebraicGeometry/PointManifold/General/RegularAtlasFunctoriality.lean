import Langlands.AlgebraicGeometry.PointManifold.General.RegularAtlasComparisonProof
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Actual morphisms and isomorphisms for universe-general regular atlases -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

variable {k : Type u} [RCLike k]
variable {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [IsAffine Y.left]
  {d e : ℕ}

namespace RegularAtlas

/-- The actual point map of a relative morphism is smooth for any two regular atlases. -/
theorem contMDiff_postcomp (A : RegularAtlas k X d) (B : RegularAtlas k Y e) (f : X ⟶ Y) :
    @ContMDiff ℝ _ (Fin d → k) _ _ (Fin d → k) _ 𝓘(ℝ, Fin d → k)
      (RingPoint k X k) _ A.chartedSpace
      (Fin e → k) _ _ (Fin e → k) _ 𝓘(ℝ, Fin e → k)
      (RingPoint k Y k) _ B.chartedSpace ∞ (fun p => p ≫ f) := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  have hid : RegularSmooth 𝓘(ℝ, Fin d → k) (fun p : RingPoint k X k => p) :=
    fun a => A.contMDiff_regularEvaluation a
  exact (B.contMDiff_iff_regularSmooth 𝓘(ℝ, Fin d → k)
    (fun p : RingPoint k X k => p ≫ f)).2 (hid.postcomp f)

/-- An actual relative isomorphism gives a diffeomorphism with its actual point maps. -/
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

/-- The forward and inverse maps are exactly postcomposition by the isomorphism. -/
theorem postcompDiffeomorph_maps
    (A : RegularAtlas k X d) (B : RegularAtlas k Y e) (f : X ≅ Y) :
    let eF := @Diffeomorph.toEquiv ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
      (Fin d → k) _ (Fin e → k) _
      𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
      (RingPoint k X k) _ A.chartedSpace
      (RingPoint k Y k) _ B.chartedSpace ∞ (A.postcompDiffeomorph B f)
    (∀ p, eF p = p ≫ f.hom) ∧ (∀ q, eF.symm q = q ≫ f.inv) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Two regular atlases on the same actual carrier are related by the identity
diffeomorphism, with both charted-space structures explicit. -/
theorem independence (A : RegularAtlas k X d) (B : RegularAtlas k X e) :
    ∃ F : @Diffeomorph ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ A.chartedSpace
        (RingPoint k X k) _ B.chartedSpace ∞,
      let eF := @Diffeomorph.toEquiv ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ A.chartedSpace
        (RingPoint k X k) _ B.chartedSpace ∞ F
      eF = Equiv.refl (RingPoint k X k) := by
  refine ⟨A.postcompDiffeomorph B (Iso.refl X), ?_⟩
  intro eF
  exact Equiv.ext fun p => Category.comp_id p

end RegularAtlas

end Langlands.AlgebraicGeometry.PointManifold.General
