import Langlands.GroupScheme.Adjoint.QuasiSplitStatement
import Langlands.GroupScheme.Adjoint.BaseChangeProof
import Langlands.GroupScheme.Absolute.BorelQuotientDescent
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.KernelCoreQuotientDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Quasi-splitness of a supplied adjoint quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace AdjointQuotientBorelImage

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A subgroup of the source mapping to a solvable group has solvable point
kernel, because the actual quotient kernel is central. -/
theorem isSolvable_of_central_kernel
    {C G A J : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (a : C ⟶ G) [Mono a.hom.hom] (r : C ⟶ J) (j : J ⟶ A)
    (hcomm : a ≫ q = r ≫ j) (hJ : IsSolvableGroupScheme J) :
    IsSolvableGroupScheme C := by
  apply (isSolvableGroupScheme_iff_isSolvable_points C).mpr
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points J).mp hJ
  let R : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X) :=
    ((yonedaGrp.map r).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
  have hcomm' : a.hom.hom ≫ q.hom.hom = r.hom.hom ≫ j.hom.hom :=
    congrArg (fun f : C ⟶ A => f.hom.hom) hcomm
  have hc (x : R.ker) : (x.val ≫ a.hom.hom) ∈
      (center G).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    apply (hq.mem_center_iff_comp_eq_one _ _).mpr
    have hx : x.val ≫ r.hom.hom = 1 := x.property
    rw [Category.assoc, hcomm', ← Category.assoc, hx, MonObj.one_comp]
  have : Group.IsSolvable R.ker := Group.isSolvable_of_comm (by
    intro x y
    apply Subtype.ext
    apply (cancel_mono a.hom.hom).mp
    change (x.val * y.val) ≫ a.hom.hom = (y.val * x.val) ≫ a.hom.hom
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact (commute_of_mem_center (hc x) (y.val ≫ a.hom.hom)).eq)
  exact Group.isSolvable_of_ker_le_range R.ker.subtype R (by simp)

/-- The reduced identity core of an affine group maps onto a connected affine
target whenever the original homomorphism is flat and locally of finite
presentation. Its range is both open and closed. -/
theorem surjective_identityCore_comp
    {N J : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType N.X.hom] [IsAffineHom N.X.hom]
    [ConnectedSpace J.X.left] [LocallyOfFiniteType J.X.hom] [IsAffineHom J.X.hom]
    (r : N ⟶ J) [Flat r.hom.hom.left]
    [LocallyOfFinitePresentation r.hom.hom.left] :
    Surjective (ReducedSubgroup.identityCoreι N ≫ r).hom.hom.left := by
  let s := ReducedSubgroup.identityCoreι N ≫ r
  have hopen : IsOpen (Set.range s.hom.hom.left) := by
    have h := r.hom.hom.left.isOpenMap _
      (ReducedSubgroup.isOpen_range_identityCoreι N)
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← Over.comp_left, ← Grp.comp_hom_hom] at h
    exact h
  obtain ⟨D, inc, fac, hic, hfac, _, hfs, _, _, _, _, _⟩ := HomImage.exists_image s
  have : IsClosedImmersion inc.hom.hom.left := hic
  have hrange : Set.range s.hom.hom.left = Set.range inc.hom.hom.left := by
    rw [← hfac]
    change Set.range (fac.hom.hom.left ≫ inc.hom.hom.left) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hfs.surj, Set.image_univ]
  have hclosed : IsClosed (Set.range s.hom.hom.left) := by
    rw [hrange]
    exact inc.hom.hom.left.isClosedEmbedding.isClosed_range
  have hr : Set.range s.hom.hom.left = Set.univ :=
    (show IsClopen (Set.range s.hom.hom.left) from ⟨hclosed, hopen⟩).eq_univ
      ⟨s.hom.hom.left (IdentityComponent.identityPoint (ReducedSubgroup.identityCore N)), _, rfl⟩
  exact ⟨Set.range_eq_univ.mp hr⟩

/-- Over an algebraically closed field, the smooth connected image of a Borel
under an actual full-centre adjoint quotient is a Borel. -/
theorem isBorelSubgroup_image
    {B G I A : GroupScheme (Spec (CommRingCat.of k))}
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (p : B ⟶ I) [Surjective p.hom.hom.left] [LocallyOfFiniteType p.hom.hom.left]
    (j : I ⟶ A) (hj : IsClosedSubgroup j)
    [Smooth I.X.hom] [ConnectedSpace I.X.left]
    (hcomm : i ≫ q = p ≫ j) : IsBorelSubgroup j := by
  have : Smooth G.X.hom := hq.isConnectedReductive.smooth
  have : IsAffineHom G.X.hom := hq.isConnectedReductive.isAffineHom
  have : IsAffineHom A.X.hom := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  have : Flat q.hom.hom.left := hq.flat
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.locallyOfFinitePresentation
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points B).mp hi.isSolvableGroupScheme
  let pPoints : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ I.X) :=
    ((yonedaGrp.map p).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
  refine ⟨hj, inferInstance, inferInstance,
    (isSolvableGroupScheme_iff_isSolvable_points I).mpr
      (Group.isSolvable_of_surjective (f := pPoints) (rationalPoints_surjective p)), ?_⟩
  intro J j' f hj' hJs hJc hJv hf
  have : Smooth J.X.hom := hJs
  have : ConnectedSpace J.X.left := hJc
  have : IsClosedImmersion j'.hom.hom.left := hj'
  have : IsAffineHom J.X.hom := by
    rw [← Over.w j'.hom.hom]
    infer_instance
  let P := SubgroupPreimage.groupScheme q j'
  let a : P ⟶ G := SubgroupPreimage.inclusion q j'
  let r : P ⟶ J := SubgroupPreimage.projection q j'
  have ha : IsClosedSubgroup a := SubgroupPreimage.isClosedSubgroup q j' hj'
  have : IsClosedImmersion a.hom.hom.left := ha
  have : IsAffineHom P.X.hom := SubgroupPreimage.isAffineHom q j' hj'
  have : LocallyOfFiniteType P.X.hom := by
    rw [← Over.w a.hom.hom]
    infer_instance
  let C := ReducedSubgroup.identityCore P
  let c : C ⟶ G := ReducedSubgroup.identityCoreι P ≫ a
  let s : C ⟶ J := ReducedSubgroup.identityCoreι P ≫ r
  have hc : IsClosedSubgroup c := by
    change IsClosedImmersion
      ((ReducedSubgroup.identityCoreι P).hom.hom.left ≫ a.hom.hom.left)
    infer_instance
  have : IsClosedImmersion c.hom.hom.left := hc
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have hpre : a ≫ q = r ≫ j' := by
    apply Grp.hom_ext
    exact (SubgroupPreimage.isPullback q j').w
  have hcs : c ≫ q = s ≫ j' := by
    dsimp only [c, s]
    rw [Category.assoc, hpre, Category.assoc]
  have hCv : IsSolvableGroupScheme C :=
    isSolvable_of_central_kernel q hq c s j' hcs hJv
  let b : B ⟶ P := quotientOvergroupHom i q p j hcomm j' f hf
  let bC : B ⟶ C := ReducedSubgroup.factorIdentityCore b
  have hbC : bC ≫ c = i := by
    dsimp only [bC, c]
    rw [← Category.assoc, ReducedSubgroup.factorIdentityCore_comp]
    exact quotientOvergroupHom_inclusion i q p j hcomm j' f hf
  have : IsIso bC := hi.maximal C c bC hc inferInstance inferInstance hCv hbC
  have : IsIso bC.hom := inferInstanceAs (IsIso ((Grp.forget₂Mon _).map bC))
  have : IsIso bC.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map bC.hom))
  have : IsIso bC.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map bC.hom.hom))
  have : Flat r.hom.hom.left := SubgroupPreimage.flat_projection q j'
  have : LocallyOfFinitePresentation r.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j') inferInstance
  have : Surjective s.hom.hom.left := surjective_identityCore_comp r
  have hproj : bC ≫ s = p ≫ f := by
    dsimp only [bC, s]
    rw [← Category.assoc, ReducedSubgroup.factorIdentityCore_comp]
    exact quotientOvergroupHom_projection i q p j hcomm j' f hf
  have : Surjective (p.hom.hom.left ≫ f.hom.hom.left) := by
    change Surjective (p ≫ f).hom.hom.left
    rw [← hproj]
    change Surjective (bC.hom.hom.left ≫ s.hom.hom.left)
    infer_instance
  have : Surjective f.hom.hom.left := Surjective.of_comp p.hom.hom.left _
  have hfclosed : IsClosedSubgroup f := IsClosedSubgroup.of_comp hj' (by rw [hf]; exact hj)
  have : IsClosedImmersion f.hom.hom.left := hfclosed
  have : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ J.X.hom
  have : IsIso f.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Grp.forget₂Mon _)

end AdjointQuotientBorelImage
/-- A supplied actual full-centre adjoint quotient preserves quasi-splitness,
without restrictions on the base field or on smoothness of the centre. -/
theorem adjointQuotientQuasiSplitStatement : AdjointQuotientQuasiSplitStatement.{u} := by
  intro k _ G A q hq hG
  have : IsAffineHom G.X.hom := hq.isConnectedReductive.isAffineHom
  have hA := hq.isAdjoint.isSemisimple.isConnectedReductive
  have : IsAffineHom A.X.hom := hA.isAffineHom
  have : Smooth A.X.hom := hA.smooth
  obtain ⟨B, i, hi⟩ := hG.exists_isGeometricBorelSubgroup
  have : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  have : Smooth B.X.hom := hi.1.smooth
  have : ConnectedSpace B.X.left := hi.1.connectedSpace
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨I, j, p, hj, hfac, _, hps, _, hpl, hIs, hIc, hIa⟩ :=
    HomImage.exists_image (i ≫ q)
  have : Surjective p.hom.hom.left := hps
  have : LocallyOfFinitePresentation p.hom.hom.left := hpl
  have : Smooth I.X.hom := hIs
  have : ConnectedSpace I.X.left := hIc
  have : IsAffineHom I.X.hom := hIa
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have hqb : IsAdjointQuotient (F.map q) :=
    adjointQuotientBaseChangeStatement k (AlgebraicClosure k) G A q hq
  have : Surjective (F.map p).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b p.hom.hom hps
  have : LocallyOfFinitePresentation (F.map p).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b p.hom.hom hpl
  have : Smooth (F.obj I).X.hom := by
    change Smooth (pullback.snd I.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj I).X.left := I.connectedSpace_baseChange_of_smooth_affine b
  have hcomm : F.map i ≫ F.map q = F.map p ≫ F.map j := by
    rw [← F.map_comp, ← F.map_comp, hfac]
  have hjb : IsBorelSubgroup (F.map j) :=
    AdjointQuotientBorelImage.isBorelSubgroup_image (F.map i) hi.2 (F.map q) hqb
      (F.map p) (F.map j) (hj.baseChange b) hcomm
  exact ⟨hA, I, j, isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hjb hj⟩

end Langlands.GroupScheme
