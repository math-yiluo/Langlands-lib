import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Derived.CentralIntersectionReduction

/-! # Unipotent radicals of actual subgroup preimages -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
  {G Q V : GroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ Q) (s : V ⟶ Q)

/-- Under an affine fppf quotient with smooth connected unipotent kernel,
the actual inverse image of a represented target radical is a source radical. -/
theorem HasSmoothConnectedUnipotentKernel.isUnipotentRadical_preimage
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q) (hs : IsUnipotentRadical s) :
    IsUnipotentRadical (SubgroupPreimage.inclusion q s) := by
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence k G
  have heq : SubgroupFunctor.range (SubgroupPreimage.inclusion q s) =
      SubgroupFunctor.range i :=
    (SubgroupPreimage.range_inclusion q s).trans (hq.radical_comap_eq hi hs)
  have : Smooth q.hom.hom.left := hq.smooth
  have : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : GeometricallyConnected (kernel q).X.hom := hq.geometricallyConnected
  have : Smooth V.X.hom := hs.smooth
  have : ConnectedSpace V.X.left := hs.connectedSpace
  have : IsAffineHom (SubgroupPreimage.groupScheme q s).X.hom :=
    SubgroupPreimage.isAffineHom q s hs.isClosedSubgroup
  have : Flat (SubgroupPreimage.projection q s).hom.hom.left :=
    SubgroupPreimage.flat_projection q s
  have : Surjective (SubgroupPreimage.projection q s).hom.hom.left :=
    SubgroupPreimage.surjective_projection q s
  have : QuasiCompact (SubgroupPreimage.projection q s).hom.hom.left :=
    SubgroupPreimage.quasiCompact_projection q s
  have : IsAffineHom (kernel (SubgroupPreimage.projection q s)).X.hom :=
    SubgroupPreimage.isAffineHom_kernel q s
  refine ⟨SubgroupPreimage.isClosedSubgroup q s hs.isClosedSubgroup,
    SubgroupPreimage.smooth q s,
    SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel q s,
    isUnipotent_of_kernel_of_quotient (SubgroupPreimage.projection q s)
      (SubgroupPreimage.isUnipotent_kernel q s hq.2.2) hs.isUnipotent,
    SubgroupPreimage.isNormal q s hs.isNormal, ?_⟩
  intro H j hj hsm hc hu hn
  rw [heq]
  exact hi.greatest H j hj hsm hc hu hn

/-- A smooth connected unipotent actual kernel retains these properties
after every extension of the original base field. -/
theorem HasSmoothConnectedUnipotentKernel.baseChange
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (K : Type u) [Field K] [Algebra k K] :
    HasSmoothConnectedUnipotentKernel
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map q) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : Smooth (kernel q).X.hom := hq.1
  have : ConnectedSpace (kernel q).X.left := hq.2.1
  have : Smooth (B.obj (kernel q)).X.hom :=
    inferInstanceAs (Smooth (pullback.snd (kernel q).X.hom b))
  have : ConnectedSpace (B.obj (kernel q)).X.left :=
    connectedSpace_baseChange_of_smooth_affine (kernel q) b
  let e : (kernel (B.map q)).X ≅ (B.obj (kernel q)).X :=
    (Grp.forget (Over (Spec (CommRingCat.of K)))).mapIso (kernelBaseChangeIso b q).symm
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  refine ⟨?_, ?_, IsUnipotent.of_iso (kernelBaseChangeIso b q).symm hq.2.2.baseChange⟩
  · rw [← e.hom.w]
    infer_instance
  · exact (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.2
      ‹ConnectedSpace (B.obj (kernel q)).X.left›

/-- The actual inverse image of a geometric radical is geometric when the
quotient has smooth connected unipotent kernel. -/
theorem HasSmoothConnectedUnipotentKernel.isGeometricUnipotentRadical_preimage
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (hs : LeviSubgroup.IsGeometricUnipotentRadical s) :
    LeviSubgroup.IsGeometricUnipotentRadical (SubgroupPreimage.inclusion q s) := by
  have hA := HasSmoothConnectedUnipotentKernel.isUnipotentRadical_preimage q s hq hs.1
  refine ⟨hA, ?_⟩
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : IsAffineHom (B.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : Smooth (B.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : ConnectedSpace (B.obj G).X.left :=
    connectedSpace_baseChange_of_smooth_affine G b
  have : IsAffineHom (B.obj Q).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd Q.X.hom b))
  have : LocallyOfFiniteType (B.obj Q).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Q.X.hom b))
  have : Flat (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have : Surjective (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  have : LocallyOfFinitePresentation (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom inferInstance
  have : QuasiCompact (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) b q.hom.hom inferInstance
  have hA' := HasSmoothConnectedUnipotentKernel.isUnipotentRadical_preimage
    (B.map q) (B.map s)
    (HasSmoothConnectedUnipotentKernel.baseChange q hq (AlgebraicClosure k)) hs.2
  let W := SubgroupPreimage.groupScheme q s
  have : IsAffineHom W.X.hom := SubgroupPreimage.isAffineHom q s hs.1.isClosedSubgroup
  have : Smooth W.X.hom := hA.smooth
  have : ConnectedSpace W.X.left := hA.connectedSpace
  have heq : SubgroupFunctor.range (B.map (SubgroupPreimage.inclusion q s)) =
      SubgroupFunctor.range (SubgroupPreimage.inclusion (B.map q) (B.map s)) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupPreimage.range_inclusion,
      SubgroupFunctor.comap_baseChange, ← SubgroupFunctor.range_baseChangeHom,
      SubgroupPreimage.range_inclusion]
  refine ⟨hA.isClosedSubgroup.baseChange b,
    (inferInstanceAs (Smooth (pullback.snd W.X.hom b))),
    connectedSpace_baseChange_of_smooth_affine W b, hA.isUnipotent.baseChange, ?_, ?_⟩
  · rw [heq]
    exact hA'.isNormal
  · intro H j hj hsm hc hu hn
    rw [heq]
    exact hA'.greatest H j hj hsm hc hu hn

end Field

end Langlands.GroupScheme
