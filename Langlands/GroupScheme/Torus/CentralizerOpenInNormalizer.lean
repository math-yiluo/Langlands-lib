import Langlands.GroupScheme.Rational.TorusNormalizerRigidity
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # The centralizer as an open subgroup of the torus normalizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace TorusConjugation

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    {t : T.toGrp ⟶ G} [Mono t.hom.hom.left]
    {I : Type u} [Fintype I] [DecidableEq I]
    (e : T.toGrp ≅ splitTorus S I)
    {U : Over S} {g : U ⟶ G.X} (hg : g ∈ (torusNormalizer t).carrier U)

/-- A restricted action is the given matrix precisely when it is so at each
residue-field point of its parameter scheme. -/
theorem actsBy_iff_forall_actsAtPoint (m : Matrix I I ℤ)
    {V : Over S} (a : V ⟶ U) :
    ActsBy e hg m a ↔ ∀ x : V.left, ActsAtPoint e hg m (a.left x) := by
  constructor
  · intro h x
    let y := V.left.fromSpecResidueField x ≫ a.left
    have hy : ActsBy e hg m (overHom (U := U) y) := by
      rw [actsBy_congr e hg m (overHom (U := U) y)
        (overHom (U := V) (V.left.fromSpecResidueField x) ≫ a) rfl]
      exact ActsBy.comp e hg h (overHom (U := V) (V.left.fromSpecResidueField x))
    have hpt := (actsBy_overHom_iff e hg y m).1 hy
    change ActsAtPoint e hg m
      (a.left ((V.left.fromSpecResidueField x)
        (IsLocalRing.closedPoint (V.left.residueField x)))) at hpt
    simpa only [Scheme.fromSpecResidueField_apply] using hpt
  · intro h
    apply actsBy_of_forall_affine
    intro A s' b x
    have hd : ∀ j, ((chartFamily e hg (b ≫ a)).coeffs j).coeff (m j) = 1 := by
      intro j
      have hu : IsUnit (((chartFamily e hg (b ≫ a)).coeffs j).coeff (m j)) := by
        by_contra hd
        obtain ⟨P, hP, hdP⟩ := exists_max_ideal_of_mem_nonunits hd
        exact (actsAtPoint_chart_iff e hg (b ≫ a) m ⟨P, hP.isPrime⟩).1
          (h (b.left ⟨P, hP.isPrime⟩)) j hdP
      have hid := (chartFamily e hg (b ≫ a)).isIdempotentElem_coeff j (m j)
      exact hu.mul_left_cancel (by rw [hid.eq, mul_one])
    have hb := (actsBy_chart_iff e hg (b ≫ a) m).2 hd _ (𝟙 _) x
    simpa only [Category.id_comp] using hb

/-- The open locus in a normalizer family where its conjugation action is the
identity on the torus. -/
def centralizerLocus : U.left.Opens :=
  ⟨{x | ActsAtPoint e hg 1 x}, by
    simpa only [eq_iff_iff, iff_true] using
      (isLocallyConstant_actsAtPoint e hg 1).isOpen_fiber True⟩

/-- Factorization through the centralizer locus is exactly all-test
centralization. -/
theorem range_subset_centralizerLocus_iff {V : Over S} (a : V ⟶ U) :
    Set.range a.left ⊆ centralizerLocus e hg ↔
      a ≫ g ∈ (torusCentralizer t).carrier V := by
  rw [← actsBy_one_iff e hg a, actsBy_iff_forall_actsAtPoint]
  exact Set.range_subset_iff

end TorusConjugation

/-- A representative of the centralizer inside a split-torus normalizer is an
open subgroup, over an arbitrary base. -/
theorem splitTorusCentralizer_isOpenImmersion {S : Scheme.{u}}
    {G N Z : GroupScheme S} {T : CommGroupScheme S}
    (t : T.toGrp ⟶ G) [Mono t.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  classical
  obtain ⟨I, _, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  have hg : n.hom.hom ∈ (torusNormalizer t).carrier N.X := by
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      Category.id_comp] using (hnrep.pointsEquiv N.X (𝟙 _)).property
  let V := TorusConjugation.centralizerLocus e hg
  have hcV : Set.range c.hom.hom.left ⊆ V := by
    apply (TorusConjugation.range_subset_centralizerLocus_iff e hg c.hom.hom).2
    simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
      Category.id_comp, SubgroupFunctor.mem_comap] using
      (hcrep.pointsEquiv Z.X (𝟙 _)).property
  let v : Z.X.left ⟶ V := IsOpenImmersion.lift V.ι c.hom.hom.left
    (by simpa only [Scheme.Opens.range_ι] using hcV)
  have hv : v ≫ V.ι = c.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  let a : Over.mk (V.ι ≫ N.X.hom) ⟶ N.X := Over.homMk V.ι
  have ha : a ≫ n.hom.hom ∈ (torusCentralizer t).carrier _ := by
    apply (TorusConjugation.range_subset_centralizerLocus_iff e hg a).1
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

/-- An open immersion of group schemes can be checked on an étale cover of
the base. -/
theorem isOpenImmersion_groupHom_of_etaleCover {S : Scheme.{u}}
    {H K : GroupScheme S} (f : H ⟶ K)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hf : ∀ a, IsOpenImmersion
      ((GroupScheme.baseChange (𝒰.f a)).map f).hom.hom.left) :
    IsOpenImmersion f.hom.hom.left := by
  let 𝒱 := 𝒰.pullback₁ K.X.hom
  let p := Sigma.desc 𝒱.f
  have : Etale p :=
    IsZariskiLocalAtSource.sigmaDesc fun a => Scheme.Cover.map_prop 𝒱 a
  have : Surjective p := inferInstanceAs (Surjective (Sigma.desc 𝒱.f))
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Etale ⊓ @Surjective)
    (g := p) ⟨inferInstance, inferInstance⟩ ?_
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

/-- A representative of the centralizer inside the normalizer of a relative
torus is an open subgroup, over an arbitrary base. -/
theorem relativeTorusCentralizer_isOpenImmersion {S : Scheme.{u}}
    {G N Z : GroupScheme S} {T : CommGroupScheme S}
    (t : T.toGrp ⟶ G) [Mono t.hom.hom.left]
    (hT : RelativeTorus.IsTorus T.toGrp)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c) :
    IsOpenImmersion c.hom.hom.left := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply isOpenImmersion_groupHom_of_etaleCover c 𝒰
  intro a
  let b := 𝒰.f a
  let B := GroupScheme.baseChange b
  have : Mono t.hom.hom := Over.mono_of_mono_left _
  have : Mono (B.map t).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map t.hom.hom))
  have : Mono (B.map t).hom.hom.left := Over.mono_left_of_mono _
  have hnbase : (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map n) := by
    change (SubgroupFunctor.range ((GroupScheme.baseChange b).map t)).normalizer.IsRepresentedBy _
    rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]
    exact hnrep.baseChange b
  have hcomap :
      ((torusCentralizer t).comap n).baseChange b =
        ((torusCentralizer t).baseChange b).comap (B.map n) := by
    ext U x
    rw [SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_comap,
      SubgroupFunctor.mem_comap, SubgroupFunctor.mem_baseChange,
      baseChangePointsEquiv_comp]
  have hcbase : ((torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).comap (B.map n)).IsRepresentedBy (B.map c) := by
    rw [torusCentralizer_baseChange, ← hcomap]
    exact hcrep.baseChange b
  exact splitTorusCentralizer_isOpenImmersion
    (T := (CommGroupScheme.baseChange b).obj T)
    (B.map t) (h𝒰 a) (B.map n) hnbase (B.map c) hcbase

/-- The canonical inclusion of a represented relative-torus centralizer into
its represented normalizer, with its open immersion and all-test preimage
property. -/
def relativeTorusCentralizerNormalizerInclusion {S : Scheme.{u}}
    {G N Z : GroupScheme S} {T : CommGroupScheme S}
    (t : T.toGrp ⟶ G) [Mono t.hom.hom.left]
    (hT : RelativeTorus.IsTorus T.toGrp)
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
  exact ⟨c, hc, relativeTorusCentralizer_isOpenImmersion t hT n hnrep c hcrep, hcrep⟩

end Langlands.GroupScheme
