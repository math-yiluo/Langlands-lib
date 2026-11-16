import Langlands.GroupScheme.Nilpotent.FiniteHom
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.ImageGenerationCommutator
import Langlands.GroupScheme.SmoothProducts

/-! # Centrality of the kernel of a smooth finite homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A smooth finite homomorphism from a smooth connected affine group has
central full scheme-theoretic kernel over an algebraically closed field. -/
theorem isCentral_kernelι_of_smooth_finite_algClosed [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (f : G ⟶ H) [IsFinite f.hom.hom.left] [Smooth f.hom.hom.left] :
    IsCentral (kernelι f) := by
  have : Smooth (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  have : Smooth ((kernel f).X ⊗ G.X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IsReduced ((kernel f).X ⊗ G.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      ((kernel f).X ⊗ G.X).left ((kernel f).X ⊗ G.X).hom
  have hc : commutatorMap (kernelι f) (𝟙 G) = 1 := by
    refine hom_ext_rationalPoints fun z => ?_
    rw [MonObj.comp_one, commutatorMap_points, Grp.id_hom_hom, Category.comp_id]
    have hk : (z ≫ fst (kernel f).X G.X ≫ (kernelι f).hom.hom) ≫ f.hom.hom = 1 :=
      (kernelPointsEquiv f _ (z ≫ fst (kernel f).X G.X)).property
    have hz := Subgroup.mem_center_iff.mp
      (hasCentralBasePointKernel_of_finiteHom f hk) (z ≫ snd (kernel f).X G.X)
    simp only [Category.assoc]
    rw [← hz, mul_inv_cancel_right, mul_inv_cancel]
  intro T x T' a g
  have h1 := commutatorMap_lift (kernelι f) (𝟙 G) (a ≫ x) g
  rw [hc, MonObj.comp_one, Grp.id_hom_hom, Category.comp_id, Category.assoc] at h1
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1.symm)

/-- Centrality of a smooth finite homomorphism's full kernel over any field. -/
theorem isCentral_kernelι_of_smooth_finite
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (f : G ⟶ H) [IsFinite f.hom.hom.left] [Smooth f.hom.hom.left] :
    IsCentral (kernelι f) := by
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  obtain ⟨hes, hef, heq⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective e := hes
  have : Flat e := hef
  have : Smooth (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom e inferInstance
  have : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom e inferInstance
  have : ConnectedSpace (B.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine e
  have : IsFinite (B.map f).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) e f.hom.hom inferInstance
  have : Smooth (B.map f).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Smooth) e f.hom.hom inferInstance
  exact isCentral_kernelι_of_baseChange e f
    (isCentral_kernelι_of_smooth_finite_algClosed (B.map f))

end Langlands.GroupScheme
