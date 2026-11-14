import Langlands.GroupScheme.Absolute.UnipotentQuotientBorels
import Langlands.GroupScheme.Absolute.NormalUnipotentParabolicContainment
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Rational.LeviPreimageUnipotentRadical

/-! # Geometric parabolics under smooth connected unipotent quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace UnipotentQuotientParabolics

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)

include hq

omit [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left] in
/-- The full actual kernel lies in every geometric parabolic over the original field. -/
theorem kernel_le_parabolic
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i := by
  have : Smooth (kernel q).X.hom := hq.1
  have : ConnectedSpace (kernel q).X.left := hq.2.1
  exact hi.normalUnipotent_le (kernelι q) (kernelι_isClosedImmersion q)
    hq.2.2 (HopfPrimitive.isNormal_range_kernelι q)

/-- A supplied fpqc closed image of a parabolic is parabolic, with its exact
full inverse image and cartesian square. -/
theorem isParabolicSubgroup_image
    {P I : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (p : P ⟶ I)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left]
    (j : I ⟶ Q) (hj : IsClosedSubgroup j)
    (hsq : i ≫ q = p ≫ j) :
    IsParabolicSubgroup j ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i ∧
      IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : Smooth P.X.hom := hi.smooth
  have : Mono i.hom.hom := hi.isClosedSubgroup.mono_overHom
  have : Mono j.hom.hom := hj.mono_overHom
  have heq := SubgroupFunctor.comap_range_eq_of_fpqc_square i q p j hsq
    (kernel_le_parabolic q hq i hi)
  have hpb := SubgroupFunctor.IsRepresentedBy.isPullback_of_comap_eq
    (F := SubgroupFunctor.range i) (E := SubgroupFunctor.range j)
    ⟨inferInstance, rfl⟩ ⟨inferInstance, rfl⟩ q p hsq heq
  have : Smooth p.hom.hom.left :=
    MorphismProperty.of_isPullback (hpb.map (Over.forget _))
      (inferInstance : Smooth q.hom.hom.left)
  have : Smooth (p.hom.hom.left ≫ I.X.hom) := by
    rw [Over.w p.hom.hom]
    infer_instance
  have hIs : Smooth I.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      p.hom.hom.left I.X.hom
  have : IsAffineHom I.X.hom := hj.isAffineHom
  refine ⟨⟨hj, hIs, ?_⟩, heq, hpb⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth (F.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : ConnectedSpace (F.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have : IsAffineHom (F.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : IsAffineHom (F.obj Q).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd Q.X.hom b))
  have : IsAffineHom (F.obj I).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd I.X.hom b))
  have : LocallyOfFiniteType (F.obj I).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd I.X.hom b))
  have : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  have : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom
      inferInstance
  have hqF := HasSmoothConnectedUnipotentKernel.baseChange q hq (AlgebraicClosure k)
  obtain ⟨B, jB, a, hjB, ha⟩ := hi.exists_isBorelSubgroup
  have : Smooth B.X.hom := hjB.smooth
  have : ConnectedSpace B.X.left := hjB.connectedSpace
  have : IsAffineHom B.X.hom := hjB.isClosedSubgroup.isAffineHom
  obtain ⟨J, c, d, hc, hd, hdf, hds, hdq, _, _, _, _⟩ :=
    HomImage.exists_image (a ≫ F.map p)
  have : Flat d.hom.hom.left := hdf
  have : Surjective d.hom.hom.left := hds
  have : QuasiCompact d.hom.hom.left := hdq
  have hcs : IsClosedSubgroup (c ≫ F.map j) := hc.comp (hj.baseChange b)
  have hsqB : jB ≫ F.map q = d ≫ (c ≫ F.map j) := by
    calc
      jB ≫ F.map q = (a ≫ F.map i) ≫ F.map q := by rw [ha]
      _ = a ≫ F.map (i ≫ q) := by rw [F.map_comp, Category.assoc]
      _ = (a ≫ F.map p) ≫ F.map j := by rw [hsq, F.map_comp, Category.assoc]
      _ = d ≫ (c ≫ F.map j) := by rw [← hd, Category.assoc]
  have hB := (UnipotentQuotientBorels.isBorelSubgroup_image
    (F.map q) hqF jB hjB d (c ≫ F.map j) hcs hsqB).1
  exact ⟨J, c ≫ F.map j, c, hB, rfl⟩

/-- Construct the actual parabolic image over the original arbitrary field. -/
theorem exists_parabolic_image
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (j : I ⟶ Q) (p : P ⟶ I),
      IsParabolicSubgroup j ∧ i ≫ q = p ≫ j ∧
      Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      QuasiCompact p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i ∧
      IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : Smooth (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : Smooth Q.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      q.hom.hom.left Q.X.hom
  have : Smooth P.X.hom := hi.smooth
  have : ConnectedSpace P.X.left := hi.connectedSpace
  have : IsAffineHom P.X.hom := hi.isClosedSubgroup.isAffineHom
  obtain ⟨I, j, p, hj, hfac, hpf, hps, hpq, hpl, _, _, _⟩ :=
    HomImage.exists_image (i ≫ q)
  have : Flat p.hom.hom.left := hpf
  have : Surjective p.hom.hom.left := hps
  have : QuasiCompact p.hom.hom.left := hpq
  obtain ⟨hP, heq, hpb⟩ := isParabolicSubgroup_image q hq i hi p j hj hfac.symm
  exact ⟨I, j, p, hP, hfac.symm, hpf, hps, hpq, hpl, heq, hpb⟩

/-- The actual preimage of every geometric parabolic is geometric parabolic. -/
theorem isParabolicSubgroup_preimage
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (j : P ⟶ Q) (hj : IsParabolicSubgroup j) :
    IsParabolicSubgroup (SubgroupPreimage.inclusion q j) := by
  have : Smooth q.hom.hom.left := hq.smooth
  have : Smooth P.X.hom := hj.smooth
  let i := SubgroupPreimage.inclusion q j
  have hi : IsClosedSubgroup i :=
    SubgroupPreimage.isClosedSubgroup q j hj.isClosedSubgroup
  refine ⟨hi, SubgroupPreimage.smooth q j, ?_⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth (F.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : ConnectedSpace (F.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have : IsAffineHom (F.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : IsAffineHom (F.obj Q).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd Q.X.hom b))
  have : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  have : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom
      inferInstance
  have hqF := HasSmoothConnectedUnipotentKernel.baseChange q hq (AlgebraicClosure k)
  obtain ⟨B, jB, a, hjB, ha⟩ := hj.exists_isBorelSubgroup
  let n := SubgroupPreimage.inclusion (F.map q) jB
  have hn : IsBorelSubgroup n :=
    UnipotentQuotientBorels.isBorelSubgroup_preimage (F.map q) hqF jB hjB
  have heq : SubgroupFunctor.range (F.map i) =
      (SubgroupFunctor.range (F.map j)).comap (F.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupPreimage.range_inclusion,
      SubgroupFunctor.comap_baseChange, ← SubgroupFunctor.range_baseChangeHom]
  have hle : SubgroupFunctor.range n ≤ SubgroupFunctor.range (F.map i) := by
    rw [heq, SubgroupPreimage.range_inclusion]
    exact SubgroupFunctor.comap_mono (SubgroupFunctor.range_le_of_factor a ha)
  have : Mono n.hom.hom := hn.isClosedSubgroup.mono_overHom
  have : Mono (F.map i).hom.hom := (hi.baseChange b).mono_overHom
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  exact ⟨_, n, f, hn, hf⟩

/-- Any closed representative of a full parabolic inverse image is parabolic. -/
theorem isParabolicSubgroup_of_range_eq_comap
    {P H : GroupScheme (Spec (CommRingCat.of k))}
    (j : P ⟶ Q) (hj : IsParabolicSubgroup j)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q) :
    IsParabolicSubgroup i :=
  (isParabolicSubgroup_preimage q hq j hj).of_range_eq hi
    ((SubgroupPreimage.range_inclusion q j).trans hrange.symm)

/-- Closed representatives of a full inverse-image subgroup are parabolic
exactly when the target subgroup is parabolic. -/
theorem isParabolicSubgroup_iff_of_range_eq_comap
    {P H : GroupScheme (Spec (CommRingCat.of k))}
    (j : P ⟶ Q) (hj : IsClosedSubgroup j)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q) :
    IsParabolicSubgroup i ↔ IsParabolicSubgroup j := by
  constructor
  · intro hP
    have : Mono i.hom.hom := hi.mono_overHom
    have : Mono j.hom.hom := hj.mono_overHom
    let hiR : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
    let hjR : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
    let p := hiR.restrictionHom hjR q hrange.le
    have hsq : i ≫ q = p ≫ j := (hiR.restrictionHom_comp hjR q hrange.le).symm
    have hpb := (hiR.isPullback_of_comap_eq hjR q p hsq hrange.symm).map
      (Over.forget _)
    have : Flat p.hom.hom.left :=
      MorphismProperty.of_isPullback hpb (inferInstance : Flat q.hom.hom.left)
    have : Surjective p.hom.hom.left :=
      MorphismProperty.of_isPullback hpb (inferInstance : Surjective q.hom.hom.left)
    have : QuasiCompact p.hom.hom.left :=
      MorphismProperty.of_isPullback hpb (inferInstance : QuasiCompact q.hom.hom.left)
    exact (isParabolicSubgroup_image q hq i hP p j hj hsq).1
  · intro hP
    exact isParabolicSubgroup_of_range_eq_comap q hq j hP i hi hrange

end UnipotentQuotientParabolics

/-- Geometric parabolic images and full inverse images through supplied smooth
connected unipotent-kernel quotients over arbitrary fields. -/
def UnipotentQuotientParabolicCorrespondenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left],
    HasSmoothConnectedUnipotentKernel q →
      (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
        IsParabolicSubgroup i →
          ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (j : I ⟶ Q) (p : P ⟶ I),
            IsParabolicSubgroup j ∧ i ≫ q = p ≫ j ∧
            Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
            QuasiCompact p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left ∧
            (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i ∧
            IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom) ∧
      (∀ (P H : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ Q) (i : H ⟶ G),
        IsClosedSubgroup j → IsClosedSubgroup i →
          SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q →
            (IsParabolicSubgroup i ↔ IsParabolicSubgroup j))

/-- The arbitrary-field geometric parabolic correspondence has no retained
Borel correspondence, conjugacy or lifting premise. -/
theorem unipotentQuotientParabolicCorrespondence :
    UnipotentQuotientParabolicCorrespondenceStatement.{u} := by
  intro k _ G Q _ _ _ _ q _ _ _ hq
  constructor
  · intro P i hi
    exact UnipotentQuotientParabolics.exists_parabolic_image q hq i hi
  · intro P H j i hj hi hrange
    exact UnipotentQuotientParabolics.isParabolicSubgroup_iff_of_range_eq_comap
      q hq j hj i hi hrange

end Langlands.GroupScheme
