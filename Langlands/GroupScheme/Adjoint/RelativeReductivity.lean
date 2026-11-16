import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.Adjoint.CenterQuotientReductiveProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Reductivity of supplied affine full-centre quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

/-- An affine full-centre fppf quotient of a reductive group scheme is reductive,
over every base scheme. -/
theorem isReductive_target {S : Scheme.{u}} {G Q : GroupScheme S} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hG : IsReductive G) [IsAffineHom Q.X.hom] : IsReductive Q := by
  have : Smooth G.X.hom := hG.smooth
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : Flat (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : Flat Q.X.hom :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  have : LocallyOfFinitePresentation (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  have hf : ∀ {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      IsConnectedReductive ((GroupScheme.baseChange b).obj Q) := by
    intro k _ b
    have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
      change IsAffineHom (pullback.snd Q.X.hom b)
      infer_instance
    have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj Q).X.hom := by
      change LocallyOfFiniteType (pullback.snd Q.X.hom b)
      infer_instance
    exact centerQuotientReductive k ((GroupScheme.baseChange b).obj G)
      ((GroupScheme.baseChange b).obj Q) ((GroupScheme.baseChange b).map q)
      (hG.isConnectedReductive_baseChange b) inferInstance inferInstance
      (hq.baseChange_center b)
  refine ⟨?_, inferInstance, fun s => (hf (geometricPoint S s)).isPseudoReductive⟩
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  exact (hf (S.fromSpecResidueField s)).smooth

/-- The supplied affine quotient meets the relative adjoint quotient interface. -/
theorem isRelativeAdjointQuotient {S : Scheme.{u}} {G Q : GroupScheme S} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hG : IsReductive G) [IsAffineHom Q.X.hom] : IsRelativeAdjointQuotient q :=
  ⟨hG, hq.isReductive_target hG, hq⟩

end RelativeRoot.IsFppfQuotient

end Langlands.GroupScheme
