import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.Torus.CommutativeReductive
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.SplitOfDomination
import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Affine fppf images of relative tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section GeneralBase

variable {S : Scheme.{u}} {G Q : GroupScheme S} (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]

include q

/-- Smoothness of a group descends through an fppf homomorphism over any base. -/
theorem smooth_target_of_surjective_flat_hom_overBase [Smooth G.X.hom] :
    Smooth Q.X.hom := by
  have hcomp : LocallyOfFinitePresentation (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : LocallyOfFinitePresentation (q.hom.hom.left ≫ Q.X.hom) := hcomp
  let : LocallyOfFinitePresentation Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  have hflat : Flat (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : Flat (q.hom.hom.left ≫ Q.X.hom) := hflat
  let : Flat Q.X.hom :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  let b := S.fromSpecResidueField s
  let F := GroupScheme.baseChange b
  let : Smooth (F.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  let : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b q.hom.hom inferInstance
  exact smooth_target_of_surjective_flat_hom (F.map q)

/-- An fppf homomorphic image of a commutative group is commutative. -/
theorem isCommMonObj_target_of_fppfHom [IsCommMonObj G.X] : IsCommMonObj Q.X := by
  let : Epi (q.hom.hom ⊗ₘ q.hom.hom) := FppfHomDescent.epi_tensorHom q
  refine ⟨?_⟩
  apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
  rw [BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
    IsCommMonObj.mul_comm_assoc]

/-- The same actual fppf target, with its descended commutative group law. -/
def commGroupSchemeTargetOfFppfHom [IsCommMonObj G.X] : CommGroupScheme S :=
  { Q with comm := isCommMonObj_target_of_fppfHom q }

@[simp]
theorem commGroupSchemeTargetOfFppfHom_toGrp [IsCommMonObj G.X] :
    (commGroupSchemeTargetOfFppfHom q).toGrp = Q := rfl

end GeneralBase

section Field

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom Q.X.hom] (hG : IsTorus G) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]

include hG q in
/-- An affine fppf homomorphic image of a torus over a field is a torus. -/
theorem IsTorus.of_fppfHom : IsTorus Q := by
  obtain ⟨K, hK, aK, hs⟩ := hG
  let : Field K := hK
  let : Algebra k K := aK
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := GroupScheme.baseChange b
  let : IsAffineHom (F.obj Q).X.hom :=
    MorphismProperty.pullback_snd Q.X.hom b inferInstance
  let : Smooth (F.obj G).X.hom := hs.smooth
  let : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  let : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b q.hom.hom inferInstance
  let : Smooth (F.obj Q).X.hom := smooth_target_of_surjective_flat_hom (F.map q)
  let : IsReduced (F.obj Q).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K (F.obj Q).X.left (F.obj Q).X.hom
  have hd : IsSchemeTheoreticallyDominant (F.map q).hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact ⟨K, hK, aK, hs.of_schematicallyDominant_hom (F.map q) hd⟩

end Field

namespace RelativeTorus

variable {S : Scheme.{u}} {G Q : GroupScheme S}
    [IsAffineHom Q.X.hom] (hG : IsTorus G) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]

include hG q in
/-- An affine fppf homomorphic image of a relative torus is a relative torus. -/
theorem IsTorus.of_fppfHom : IsTorus Q := by
  let : IsCommMonObj G.X := hG.isCommMonObj
  let Qc := commGroupSchemeTargetOfFppfHom q
  let : IsAffineHom Qc.X.hom := (inferInstance : IsAffineHom Q.X.hom)
  apply relativeTorus_of_commutative_reductive Qc
  let : Smooth G.X.hom := hG.smooth
  refine ⟨smooth_target_of_surjective_flat_hom_overBase q, inferInstance, ?_⟩
  intro s
  let b := geometricPoint S s
  let F := GroupScheme.baseChange b
  let : IsAffineHom (F.obj Q).X.hom :=
    MorphismProperty.pullback_snd Q.X.hom b inferInstance
  let : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  let : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      b q.hom.hom inferInstance
  exact ((hG.baseChange b).isTorus.of_fppfHom (F.map q)).isConnectedReductive_of_fieldSplitting
    |>.isPseudoReductive

end RelativeTorus
end Langlands.GroupScheme
