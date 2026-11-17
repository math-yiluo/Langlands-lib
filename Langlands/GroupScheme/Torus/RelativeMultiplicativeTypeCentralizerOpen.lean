import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerOpen
import Langlands.GroupScheme.Torus.DiagonalizableNormalizer
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange

/-! # Open centralizers of subgroups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace DiagonalizableCentralizer

open Corepresented CharacterAction

/-- The represented centralizer of a diagonalizable subgroup is open in its
represented normalizer when the subgroup has projective quotient coordinates. -/
theorem isOpenImmersion_of_projective
    {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ groupScheme F e) [Mono j.hom.hom]
    {I : Ideal B}
    (hI : ∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
      y ∈ (SubgroupFunctor.range j).carrier U ↔
        ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0)
    [Module.Projective R (B ⧸ I)]
    {N Z : GroupScheme (Spec R)} (n : N ⟶ groupScheme F e)
    (hnrep : (SubgroupFunctor.range j).normalizer.IsRepresentedBy n)
    (c : Z ⟶ N)
    (hcrep : ((SubgroupFunctor.range j).centralizer.comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  classical
  have hg : n.hom.hom ∈ (SubgroupFunctor.range j).normalizer.carrier N.X := by
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      Category.id_comp] using (hnrep.pointsEquiv N.X (𝟙 _)).property
  let V := openLocus e j hI hg
  have hcV : Set.range c.hom.hom.left ⊆ V := by
    apply (range_subset_openLocus_iff e j hI hg c.hom.hom).2
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      Category.id_comp, SubgroupFunctor.mem_comap] using
      (hcrep.pointsEquiv Z.X (𝟙 _)).property
  let v : Z.X.left ⟶ V := IsOpenImmersion.lift V.ι c.hom.hom.left
    (by simpa only [Scheme.Opens.range_ι] using hcV)
  have hv : v ≫ V.ι = c.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  let a : Over.mk (V.ι ≫ N.X.hom) ⟶ N.X := Over.homMk V.ι
  have ha : a ≫ n.hom.hom ∈ (SubgroupFunctor.range j).centralizer.carrier _ := by
    apply (range_subset_openLocus_iff e j hI hg a).1
    rintro _ ⟨x, rfl⟩
    exact x.property
  obtain ⟨d, hd⟩ : ∃ d : Over.mk (V.ι ≫ N.X.hom) ⟶ Z.X,
      d ≫ c.hom.hom = a := by
    have hm : a ∈ (SubgroupFunctor.range c).carrier _ := by
      rw [hcrep.2]
      exact ha
    exact hm
  have hdc : d.left ≫ c.hom.hom.left = V.ι :=
    congrArg (fun f => f.left) hd
  let : Mono c.hom.hom := hcrep.1
  let : Mono c.hom.hom.left := Over.mono_left_of_mono _
  let eZ : Z.X.left ≅ V :=
    { hom := v
      inv := d.left
      hom_inv_id := by
        rw [← cancel_mono c.hom.hom.left, Category.assoc, hdc, hv, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono V.ι, Category.assoc, hv, hdc, Category.id_comp] }
  have : IsIso v := eZ.isIso_hom
  rw [← hv]
  infer_instance

end DiagonalizableCentralizer

open Corepresented

/-- Over an affine base, the centralizer of a closed diagonalizable subgroup
is open in its represented normalizer. -/
theorem diagonalizableCentralizer_isOpenImmersion_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G N Z : GroupScheme (Spec R)} [IsAffine G.X.left]
    (j : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hj : IsClosedSubgroup j)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range j).normalizer.IsRepresentedBy n)
    (c : Z ⟶ N)
    (hcrep : ((SubgroupFunctor.range j).centralizer.comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let e := AffineCoordinates.corepresentation G
  let j' := AffineCoordinates.coordinateHom j
  let : IsClosedImmersion j'.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (AffineCoordinates.coordinateHom j).hom.hom.left)
  let : Mono j'.hom.hom.left :=
    SurjectiveOnStalks.mono_of_injective j'.hom.hom.left.isClosedEmbedding.injective
  let : Mono j'.hom.hom := Over.mono_of_mono_left _
  obtain ⟨I, hI⟩ := exists_ideal_range j'
  let hcut := isCutOutBy_range hI
  have hrep₁ : (SubgroupFunctor.range j').IsRepresentedBy j' :=
    ⟨inferInstance, rfl⟩
  have hrep₂ : (SubgroupFunctor.range j').IsRepresentedBy (cutHom hcut) :=
    isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_range hI)
  let eH : (Diagonalizable.groupScheme R M).toGrp ≅ cutGroupScheme hcut :=
    hrep₁.isoOfIsRepresentedBy hrep₂
  let eA : CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I) ≅
      ((algΓ R).obj (Diagonalizable.groupScheme R M).X).unop :=
    (affineSectionsIso (CommAlgCat.of R (AffineCoordinates.algebra G ⧸ I))).symm ≪≫
      ((algΓ R).mapIso ((Grp.forget _).mapIso eH)).unop
  let : Module.Projective R
      (((algΓ R).obj (Diagonalizable.groupScheme R M).X).unop) :=
    Module.Projective.of_equiv
      (affineSectionsAlgEquiv (Diagonalizable.algebra R M)).symm.toLinearEquiv
  let : Module.Projective R (AffineCoordinates.algebra G ⧸ I) :=
    Module.Projective.of_equiv (CommAlgCat.algEquivOfIso eA).symm.toLinearEquiv
  have hnormalizer : (SubgroupFunctor.range j').normalizer =
      (SubgroupFunctor.range j).normalizer.comap (AffineCoordinates.groupSchemeIso G).hom := by
    simpa only [j', AffineCoordinates.coordinateHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using SubgroupFunctor.normalizer_range_eq_comap_of_iso
        j' (AffineCoordinates.groupSchemeIso G)
  have hcentralizer : (SubgroupFunctor.range j').centralizer =
      (SubgroupFunctor.range j).centralizer.comap (AffineCoordinates.groupSchemeIso G).hom := by
    simpa only [j', AffineCoordinates.coordinateHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using SubgroupFunctor.centralizer_range_eq_comap_of_iso
        j' (AffineCoordinates.groupSchemeIso G)
  have hncoord : (SubgroupFunctor.range j').normalizer.IsRepresentedBy
      (AffineCoordinates.coordinateHom n) := by
    rw [hnormalizer]
    exact hnrep.comp_iso (AffineCoordinates.groupSchemeIso G).symm
  have hcomp : AffineCoordinates.coordinateHom n ≫ (AffineCoordinates.groupSchemeIso G).hom = n := by
    simp only [AffineCoordinates.coordinateHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hccoord : ((SubgroupFunctor.range j').centralizer.comap
      (AffineCoordinates.coordinateHom n)).IsRepresentedBy c := by
    rw [hcentralizer, ← SubgroupFunctor.comap_comp, hcomp]
    exact hcrep
  exact DiagonalizableCentralizer.isOpenImmersion_of_projective
    e j' hI (AffineCoordinates.coordinateHom n) hncoord c hccoord

/-- The affine-base result applies to any diagonalizable model of the subgroup. -/
theorem diagonalizableCentralizer_isOpenImmersion_overSpec
    {R : CommRingCat.{u}} {G H N Z : GroupScheme (Spec R)} [IsAffine G.X.left]
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n)
    (c : Z ⟶ N)
    (hcrep : ((SubgroupFunctor.range i).centralizer.comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let e' : H ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  let j := e'.inv ≫ i
  have hj : IsClosedSubgroup j := IsClosedSubgroup.iso_comp e'.symm hi
  have hrange : SubgroupFunctor.range j = SubgroupFunctor.range i :=
    SubgroupFunctor.range_iso_comp e'.symm i
  exact diagonalizableCentralizer_isOpenImmersion_overRing j hj n
    (by rwa [hrange]) c (by rwa [hrange])

/-- A represented centralizer is open in a represented normalizer for a
closed diagonalizable subgroup over an arbitrary base. -/
theorem diagonalizableCentralizer_isOpenImmersion
    {S : Scheme.{u}} {G N Z : GroupScheme S} {T : CommGroupScheme S}
    [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeMultiplicativeType.IsDiagonalizable T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    S.affineOpenCover.openCover.changeProp (fun _ => inferInstance)
  apply isOpenImmersion_groupHom_of_etaleCover c 𝒰
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  have hnbase : (SubgroupFunctor.range (B.map t)).normalizer.IsRepresentedBy (B.map n) := by
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
    exact hnrep.baseChange b
  have hcomap : ((torusCentralizer t).comap n).baseChange b =
      ((torusCentralizer t).baseChange b).comap (B.map n) := by
    ext U x
    rw [SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_comap,
      SubgroupFunctor.mem_comap, SubgroupFunctor.mem_baseChange,
      baseChangePointsEquiv_comp]
  have hcbase : ((SubgroupFunctor.range (B.map t)).centralizer.comap (B.map n)).IsRepresentedBy
      (B.map c) := by
    rw [← torusCentralizer_eq_centralizer_range
      (T := (CommGroupScheme.baseChange b).obj T), torusCentralizer_baseChange, ← hcomap]
    exact hcrep.baseChange b
  exact diagonalizableCentralizer_isOpenImmersion_overSpec
    (R := S.affineOpenCover.X k) (B.map t) (hT.baseChange b) (ht.baseChange b)
    (B.map n) hnbase (B.map c) hcbase

/-- Open immersions of group schemes descend along any fppf base cover. -/
theorem isOpenImmersion_groupHom_of_fppfCover {S : Scheme.{u}}
    {H K : GroupScheme S} (f : H ⟶ K)
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (hf : ∀ a, IsOpenImmersion
      ((GroupScheme.baseChange (𝒰.f a)).map f).hom.hom.left) :
    IsOpenImmersion f.hom.hom.left := by
  let 𝒱 := 𝒰.pullback₁ K.X.hom
  let p := Sigma.desc 𝒱.f
  have : Flat p := IsZariskiLocalAtSource.sigmaDesc fun a => (Scheme.Cover.map_prop 𝒱 a).1
  have : LocallyOfFinitePresentation p :=
    IsZariskiLocalAtSource.sigmaDesc fun a => (Scheme.Cover.map_prop 𝒱 a).2
  have : Surjective p := inferInstanceAs (Surjective (Sigma.desc 𝒱.f))
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (g := p) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ ?_
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover 𝒱.X) fun a => ?_
  change IsOpenImmersion
    (pullback.snd (pullback.snd f.hom.hom.left p) (Sigma.ι 𝒱.X a))
  have hbig := ((IsPullback.of_hasPullback
    (pullback.snd f.hom.hom.left p) (Sigma.ι 𝒱.X a)).flip.paste_vert
      (IsPullback.of_hasPullback f.hom.hom.left p).flip).flip
  have hi : Sigma.ι 𝒱.X a ≫ p = 𝒱.f a := Sigma.ι_comp_desc _ _
  rw [hi] at hbig
  rw [← hbig.isoPullback_hom_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)]
  have hpb := (baseChange_map_isPullback (𝒰.f a) f).flip
  have hfa := hf a
  rw [← hpb.isoPullback_hom_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)] at hfa
  exact hfa

/-- A representative of the centralizer of a closed subgroup of
multiplicative type is open in its represented normalizer. -/
theorem relativeMultiplicativeTypeCentralizer_isOpenImmersion
    {S : Scheme.{u}} {G N Z : GroupScheme S} {T : CommGroupScheme S}
    [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeMultiplicativeType.IsMultiplicativeType T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply isOpenImmersion_groupHom_of_fppfCover c 𝒰
  intro a
  let b := 𝒰.f a
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hnbase : (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map n) := by
    change (SubgroupFunctor.range (B.map t)).normalizer.IsRepresentedBy _
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
    exact hnrep.baseChange b
  have hcomap : ((torusCentralizer t).comap n).baseChange b =
      ((torusCentralizer t).baseChange b).comap (B.map n) := by
    ext U x
    rw [SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_comap,
      SubgroupFunctor.mem_comap, SubgroupFunctor.mem_baseChange,
      baseChangePointsEquiv_comp]
  have hcbase : ((torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).comap (B.map n)).IsRepresentedBy (B.map c) := by
    rw [torusCentralizer_baseChange, ← hcomap]
    exact hcrep.baseChange b
  exact diagonalizableCentralizer_isOpenImmersion
    (T := (CommGroupScheme.baseChange b).obj T)
    (B.map t) (h𝒰 a) (ht.baseChange b) (B.map n) hnbase (B.map c) hcbase

/-- The canonical open inclusion of a represented multiplicative-type
centralizer into its represented normalizer, with its all-test preimage property. -/
def relativeMultiplicativeTypeCentralizerNormalizerInclusion
    {S : Scheme.{u}} {G N Z : GroupScheme S} {T : CommGroupScheme S}
    [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeMultiplicativeType.IsMultiplicativeType T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (z : Z ⟶ G) (hzrep : (torusCentralizer t).IsRepresentedBy z) :
    {c : Z ⟶ N // c ≫ n = z ∧ IsOpenImmersion c.hom.hom.left ∧
      ((torusCentralizer t).comap n).IsRepresentedBy c} := by
  let c := hnrep.factorHom z
    (by rw [hzrep.2]; exact torusCentralizer_le_torusNormalizer t)
  have hc : c ≫ n = z := hnrep.factorHom_comp _ _
  have hc' : c.hom.hom ≫ n.hom.hom = z.hom.hom :=
    congrArg (fun f => f.hom.hom) hc
  have : Mono z.hom.hom := hzrep.1
  have hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c := by
    refine ⟨mono_of_mono_fac hc', ?_⟩
    ext U x
    rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, ← hzrep.2,
      SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Category.assoc, hc']⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hnrep.1.right_cancellation _ _
        (by rw [Category.assoc, hc']; exact hy)⟩
  exact ⟨c, hc,
    relativeMultiplicativeTypeCentralizer_isOpenImmersion t hT ht n hnrep c hcrep, hcrep⟩

end Langlands.GroupScheme
