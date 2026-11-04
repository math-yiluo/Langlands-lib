import Langlands.GroupScheme.Rational.SplitUnipotentExtensionSection
import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Closed torus lifts through split-unipotent quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G U Q H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (n : U ⟶ G) [Mono n.hom.hom] (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hU : IsUnipotent U) (hUsplit : RelativeRoot.IsSplitUnipotent U)
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    (j : H ⟶ Q) (hj : IsClosedSubgroup j) (hH : IsTorus H)

include hq hU hUsplit hstable hlinear hj hH in
/-- A closed torus has a homomorphic lift through an affine quotient with
smooth connected split-unipotent full kernel, retaining the two exact inputs. -/
theorem IsTorus.exists_splitUnipotentQuotientLift :
    ∃ l : H ⟶ G, l ≫ q = j := by
  let : IsSeparated Q.X.hom := fieldSeparated k Q
  let : QuasiCompact q.hom.hom.left := by
    have hc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hc
    exact QuasiCompact.of_comp _ Q.X.hom
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
  let : ConnectedSpace H.X.left := hH.connectedSpace
  let : Smooth (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.smooth q j
  let : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj
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
    hstable hlinear H hH (SubgroupPreimage.groupScheme q j) p hP hPsplit
  refine ⟨s ≫ SubgroupPreimage.inclusion q j, ?_⟩
  rw [Category.assoc, subgroupIntersection_condition,
    ← Category.assoc, hs, Category.id_comp]

/-- A chosen original-field lift of the specified closed torus homomorphism. -/
def IsTorus.splitUnipotentQuotientLift : H ⟶ G :=
  Classical.choose
    (hH.exists_splitUnipotentQuotientLift n q hq hU hUsplit hstable hlinear j hj)

/-- The chosen lift has the specified composite with the original quotient. -/
theorem IsTorus.splitUnipotentQuotientLift_comp :
    hH.splitUnipotentQuotientLift n q hq hU hUsplit hstable hlinear j hj ≫ q = j :=
  Classical.choose_spec
    (hH.exists_splitUnipotentQuotientLift n q hq hU hUsplit hstable hlinear j hj)

end Langlands.GroupScheme
