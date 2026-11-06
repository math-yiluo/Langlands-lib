import Langlands.GroupScheme.Lie.TorusLieCentralizerStatements
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.Intersection
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Tori centralizing Lie elements in characteristic zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Tori and Lie centralizers in characteristic zero.** The preimage of the closed
Lie-element centralizer under a torus homomorphism is smooth by Cartier's theorem and has
full tangent space, so it is the whole connected torus. -/
theorem charZeroTorusLieCentralizer : CharZeroTorusLieCentralizerStatement.{u} := by
  intro k _ _ G _ _ T j hT Y hY
  have : Smooth T.toGrp.X.hom := hT.smooth
  have : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  have : IsAffine T.toGrp.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  obtain ⟨C, i, hrep, hi⟩ := Lie.elementCentralizer_isClosedRepresentable G Y
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom C.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hcl : IsClosedSubgroup (SubgroupPreimage.inclusion j i) :=
    SubgroupPreimage.isClosedSubgroup j i hi
  have : IsClosedImmersion (SubgroupPreimage.inclusion j i).hom.hom.left := hcl
  have : IsAffineHom (SubgroupPreimage.groupScheme j i).X.hom :=
    SubgroupPreimage.isAffineHom j i hi
  have : LocallyOfFiniteType (SubgroupPreimage.groupScheme j i).X.hom := by
    rw [← Over.w (SubgroupPreimage.inclusion j i).hom.hom]
    infer_instance
  have : Smooth (SubgroupPreimage.groupScheme j i).X.hom :=
    affineCartierSmooth k _ inferInstance inferInstance
  have hsurj : Function.Surjective
      (Lie.targetMapLinear (SubgroupPreimage.inclusion j i) k) := by
    intro t
    have h := hY t.toMul
    rw [Lie.elementCentralizerLie, SubgroupFunctor.lie_eq_range _ _ i hrep] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨Additive.ofMul (Lie.kernelIntersectionLift j i k t.toMul c.toMul
      (congrArg (fun z => z.toMul.val) hc).symm), ?_⟩
    apply Additive.toMul.injective
    exact Lie.kernelIntersectionLift_fst j i k _ _ _
  have : IsIso (SubgroupPreimage.inclusion j i) :=
    Lie.isIso_of_surjective_targetMapLinear _ hcl hsurj
  rw [← hrep.2]
  intro U x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2
    ⟨t ≫ inv (SubgroupPreimage.inclusion j i).hom.hom ≫
      (SubgroupPreimage.projection j i).hom.hom, ?_⟩
  rw [Category.assoc, Category.assoc, ← (SubgroupPreimage.isPullback j i).w,
    IsIso.inv_hom_id_assoc]

end Langlands.GroupScheme
