import Langlands.GroupScheme.Rational.SplitUnipotentQuotientTorusLift
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof

/-! # Arbitrary torus homomorphisms lift through split-unipotent quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G U Q H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (n : U ⟶ G) [Mono n.hom.hom] (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hU : IsUnipotent U) (hUsplit : RelativeRoot.IsSplitUnipotent U)
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (j : H ⟶ Q) (hH : IsTorus H)

include hq hU hUsplit hstable hH in
/-- Every torus homomorphism lifts through an affine quotient with smooth
connected split-unipotent full kernel, given the stable-vector proposition. -/
theorem IsTorus.exists_splitUnipotentQuotientHomLift :
    ∃ l : H ⟶ G, l ≫ q = j := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  let : IsAffineHom q.hom.hom.left := inferInstance
  let : QuasiCompact q.hom.hom.left := inferInstance
  have hrep : (SubgroupFunctor.range n).IsRepresentedBy n :=
    ⟨inferInstance, rfl⟩
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hrep inferInstance
  let : Surjective q.hom.hom.left := hq.2.1
  let : Smooth (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) inferInstance
  let : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  let : ConnectedSpace (kernel q).X.left :=
    KernelRepresentative.connectedSpace q n hq.2.2.2
  let : GeometricallyConnected (kernel q).X.hom :=
    geometricallyConnected_of_connected (kernel q)
  let : Smooth H.X.hom := hH.smooth
  let : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  let : IsAffineHom H.X.hom := inferInstance
  let : ConnectedSpace H.X.left := hH.connectedSpace
  let : Smooth (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.smooth q j
  let : IsAffineHom (SubgroupPreimage.projection q j).hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j) inferInstance
  let : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom := by
    rw [← Over.w (SubgroupPreimage.projection q j).hom.hom]
    infer_instance
  let : ConnectedSpace (SubgroupPreimage.groupScheme q j).X.left :=
    SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q j
  let p := SubgroupPreimage.projection q j
  let : Smooth p.hom.hom.left := SubgroupPreimage.smooth_projection q j
  let : Surjective p.hom.hom.left := SubgroupPreimage.surjective_projection q j
  let : ConnectedSpace (kernel p).X.left :=
    (Scheme.homeoOfIso
      ((Over.forget _).mapIso (SubgroupPreimage.kernelOverIso q j))).connectedSpace_iff.2
        (by change ConnectedSpace (kernel q).X.left; infer_instance)
  have hK : IsUnipotent (kernel q) :=
    KernelRepresentative.isUnipotent q n hq.2.2.2 hU
  have hKsplit : RelativeRoot.IsSplitUnipotent (kernel q) :=
    hUsplit.of_iso (KernelRepresentative.iso q n hq.2.2.2).symm
  have hP : IsUnipotent (kernel p) := SubgroupPreimage.isUnipotent_kernel q j hK
  have hPsplit : RelativeRoot.IsSplitUnipotent (kernel p) :=
    hKsplit.of_iso (SubgroupPreimage.kernelIso q j).symm
  obtain ⟨s, hs⟩ := TorusUnipotentExtension.exists_section_of_smooth_kernel
    hstable RelativeRoot.torusVectorActionLinearization H hH
      (SubgroupPreimage.groupScheme q j) p hP hPsplit
  refine ⟨s ≫ SubgroupPreimage.inclusion q j, ?_⟩
  rw [Category.assoc, subgroupIntersection_condition,
    ← Category.assoc, hs, Category.id_comp]

/-- A chosen lift of the specified torus homomorphism over the original field. -/
def IsTorus.splitUnipotentQuotientHomLift : H ⟶ G :=
  Classical.choose
    (hH.exists_splitUnipotentQuotientHomLift n q hq hU hUsplit hstable j)

/-- The chosen lift has exactly the specified composite with the quotient. -/
theorem IsTorus.splitUnipotentQuotientHomLift_comp :
    hH.splitUnipotentQuotientHomLift n q hq hU hUsplit hstable j ≫ q = j :=
  Classical.choose_spec
    (hH.exists_splitUnipotentQuotientHomLift n q hq hU hUsplit hstable j)

variable [PerfectField k] [IsAffineHom U.X.hom]

include hq hU hstable hH in
/-- Over a perfect field, smooth connected affine unipotence supplies splitness. -/
theorem IsTorus.exists_perfectFieldUnipotentQuotientHomLift :
    ∃ l : H ⟶ G, l ≫ q = j := by
  have hsplit : RelativeRoot.IsSplitUnipotent U :=
    perfectFieldUnipotentSplit k U inferInstance hU
  exact hH.exists_splitUnipotentQuotientHomLift n q hq hU hsplit hstable j

include hq hU hstable in
/-- Every actual cocharacter lifts over the same perfect field. -/
theorem exists_cocharacter_lift_of_perfectField_unipotent_kernel
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Q) :
    ∃ l : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, l ≫ q = χ :=
  isSplitTorus_gm.isTorus.exists_perfectFieldUnipotentQuotientHomLift
    n q hq hU hstable χ

end Langlands.GroupScheme
