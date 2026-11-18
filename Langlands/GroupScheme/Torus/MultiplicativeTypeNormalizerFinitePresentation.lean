import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.GroupScheme.Torus.DiagonalizableFppfQuotient
import Langlands.GroupScheme.Torus.IsomorphismLocus
import Langlands.GroupScheme.Torus.MultiplicativeTypeClosedNormalizer
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Finite presentation of multiplicative-type normalizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem normalizer_range_locallyOfFinitePresentation_overSpec
    {R : CommRingCat.{u}} {H G N : GroupScheme (Spec R)}
    [IsAffineHom H.X.hom] [Flat H.X.hom] [Module.Projective R ((algΓ R).obj H.X).unop]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) [LocallyOfFinitePresentation i.hom.hom.left]
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    LocallyOfFinitePresentation n.hom.hom.left := by
  let d := ConjugationInto.productInclusion i i
  let : IsClosedImmersion d.left := ConjugationInto.productInclusion_isClosedImmersion i i hi
  let : LocallyOfFinitePresentation d.left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback (ConjugationInto.conjugationHom i) i.hom.hom).map
        (Over.forget (Spec R))).flip)
      (inferInstance : LocallyOfFinitePresentation i.hom.hom.left)
  let L := Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation.model H.X d
  have hfactor (U : Over (Spec R)) (g : U ⟶ G.X) :
      (∃ z : U ⟶ L.source, z ≫ L.ι = g) ↔ ConjugationInto.Holds i i g :=
    (L.represents U g).trans (ConjugationInto.holds_iff_factors i i g).symm
  let invG := GrpObj.inv (X := G.X)
  let j := L.ι
  let j' := j ≫ invG
  let m : pullback j j' ⟶ G.X := pullback.fst j j' ≫ j
  let : IsClosedImmersion j.left := L.isClosedImmersion
  let : LocallyOfFinitePresentation j.left := L.locallyOfFinitePresentation
  let : IsIso invG.left := ((Over.forget _).mapIso (asIso invG)).isIso_hom
  have hj' : IsClosedImmersion j'.left := by
    change IsClosedImmersion (j.left ≫ invG.left)
    infer_instance
  have hj'fp : LocallyOfFinitePresentation j'.left := by
    change LocallyOfFinitePresentation (j.left ≫ invG.left)
    infer_instance
  have hp := ((IsPullback.of_hasPullback j j').map (Over.forget _)).flip
  let : IsClosedImmersion (pullback.fst j j').left := MorphismProperty.of_isPullback hp hj'
  let : LocallyOfFinitePresentation (pullback.fst j j').left :=
    MorphismProperty.of_isPullback hp hj'fp
  let : IsClosedImmersion m.left := inferInstanceAs
    (IsClosedImmersion ((pullback.fst j j').left ≫ j.left))
  let : LocallyOfFinitePresentation m.left := inferInstanceAs
    (LocallyOfFinitePresentation ((pullback.fst j j').left ≫ j.left))
  let : Mono m := Over.mono_of_mono_left m
  let F := (SubgroupFunctor.range i).normalizer
  have hm (U : Over (Spec R)) (g : U ⟶ G.X) :
      g ∈ F.carrier U ↔ ∃ y : U ⟶ pullback j j', y ≫ m = g := by
    have hnormal :
        g ∈ F.carrier U ↔ ConjugationInto.Holds i i g ∧ ConjugationInto.Holds i i g⁻¹ := by
      rw [show F = (SubgroupFunctor.range i).normalizer from rfl, SubgroupFunctor.mem_normalizer]
      constructor
      · intro h
        exact ⟨fun V a x => (h V a _ (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)).2,
          fun V a x => by
            simpa only [GrpObj.comp_inv, inv_inv] using
              (h V a _ (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)).1⟩
      · rintro ⟨h, hinv⟩ V a z hz
        obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
        exact ⟨by simpa only [GrpObj.comp_inv, inv_inv] using hinv V a x, h V a x⟩
    rw [hnormal, ← hfactor, ← hfactor]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      change a ≫ j = g at ha
      change b ≫ j = g⁻¹ at hb
      have hab : a ≫ j = b ≫ j' := by
        rw [show j' = j ≫ invG from rfl, ← Category.assoc, hb, ha]
        exact (inv_inv g).symm
      exact ⟨pullback.lift a b hab, by simp only [m, pullback.lift_fst_assoc, ha]⟩
    · rintro ⟨y, hy⟩
      refine ⟨⟨y ≫ pullback.fst j j', by simpa only [Category.assoc] using hy⟩,
        ⟨y ≫ pullback.snd j j', ?_⟩⟩
      have heq : ((y ≫ pullback.snd j j') ≫ j) ≫ invG = g := by
        rw [Category.assoc, Category.assoc, ← show j' = j ≫ invG from rfl,
          ← pullback.condition, ← Category.assoc]
        exact hy
      have hg := congrArg (fun p : U ⟶ G.X => p⁻¹) heq
      change (((y ≫ pullback.snd j j') ≫ j)⁻¹)⁻¹ = g⁻¹ at hg
      simpa only [inv_inv] using hg
  let n' := F.representingHom m hm
  have hn' : F.IsRepresentedBy n' := F.isRepresentedBy_representingHom m hm
  let e := hn.isoOfIsRepresentedBy hn'
  have : IsIso e.hom.hom.hom.left :=
    ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).isIso_hom
  have he : e.hom.hom.hom.left ≫ m.left = n.hom.hom.left := by
    have hw := congrArg (fun f : N ⟶ G => f.hom.hom.left) (hn.isoOfIsRepresentedBy_hom_comp hn')
    change e.hom.hom.hom.left ≫ (F.representingHom m hm).hom.hom.left = _ at hw
    rwa [F.representingHom_hom m hm] at hw
  rw [← he]
  infer_instance

open RelativeMultiplicativeType in
private theorem normalizer_range_locallyOfFinitePresentation_of_diagonalizable_overSpec
    {R : CommRingCat.{u}} {H G N : GroupScheme (Spec R)} [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsDiagonalizable H)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    LocallyOfFinitePresentation n.hom.hom.left := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  let e' : H ≅ (Diagonalizable.groupScheme R Λ).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) Λ
  let i' := e'.inv ≫ i
  let : Flat (Diagonalizable.groupScheme R Λ).toGrp.X.hom := Diagonalizable.flat_structure R Λ
  let : Module.Free R (((algΓ R).obj (Diagonalizable.groupScheme R Λ).toGrp.X).unop) :=
    Diagonalizable.free_coordinateModule R Λ
  let : LocallyOfFinitePresentation (Diagonalizable.groupScheme R Λ).toGrp.X.hom :=
    Diagonalizable.locallyOfFinitePresentation R Λ
  let : LocallyOfFinitePresentation (i'.hom.hom.left ≫ G.X.hom) := by
    rw [Over.w i'.hom.hom]
    infer_instance
  let : LocallyOfFinitePresentation i'.hom.hom.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp _ G.X.hom
  apply normalizer_range_locallyOfFinitePresentation_overSpec i'
    (IsClosedSubgroup.iso_comp e'.symm hi) n
  change (SubgroupFunctor.range (e'.symm.hom ≫ i)).normalizer.IsRepresentedBy n
  rwa [SubgroupFunctor.range_iso_comp e'.symm i]

set_option backward.isDefEq.respectTransparency false in
private theorem normalizer_range_locallyOfFinitePresentation_fppfLocal
    {S : Scheme.{u}} {H G N : GroupScheme S} (i : H ⟶ G)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n)
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (h : ∀ k, let B := baseChange (𝒰.f k)
      (SubgroupFunctor.range (B.map i)).normalizer.IsRepresentedBy (B.map n) →
        LocallyOfFinitePresentation (B.map n).hom.hom.left) :
    LocallyOfFinitePresentation n.hom.hom.left := by
  have : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  have : Precoverage.HasPullbacks Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Precoverage.HasPullbacks
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  let 𝒱 := 𝒰.pullback₁ G.X.hom
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun k => ?_
  let b := 𝒰.f k
  change LocallyOfFinitePresentation (pullback.snd n.hom.hom.left (pullback.fst G.X.hom b))
  have hp := TorusIsomorphismLocus.underlying_isPullback b n
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)
    hp.isoPullback.hom, hp.isoPullback_hom_snd]
  have hn' := hn.baseChange b
  rw [SubgroupFunctor.normalizer_baseChange, ← SubgroupFunctor.range_baseChangeHom] at hn'
  exact h k hn'

open RelativeMultiplicativeType in
private theorem normalizer_range_locallyOfFinitePresentation_of_diagonalizable
    {S : Scheme.{u}} {H G N : GroupScheme S} [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : IsDiagonalizable H)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    LocallyOfFinitePresentation n.hom.hom.left := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply normalizer_range_locallyOfFinitePresentation_fppfLocal i n hn 𝒰
  intro k
  dsimp only
  intro hn'
  let b := S.affineOpenCover.f k
  let B := baseChange b
  let : LocallyOfFinitePresentation (B.obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom b)
    infer_instance
  exact normalizer_range_locallyOfFinitePresentation_of_diagonalizable_overSpec
    (R := S.affineOpenCover.X k) (B.map i) (hi.baseChange b) (hH.baseChange b) (B.map n) hn'

/-- Every representative of a closed multiplicative-type normalizer has locally
finitely presented inclusion into a locally finitely presented ambient group. -/
theorem normalizer_range_locallyOfFinitePresentation_of_multiplicativeType
    {S : Scheme.{u}} {H G N : GroupScheme S} [LocallyOfFinitePresentation G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (n : N ⟶ G) (hn : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    LocallyOfFinitePresentation n.hom.hom.left := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply normalizer_range_locallyOfFinitePresentation_fppfLocal i n hn 𝒰
  intro k
  dsimp only
  intro hn'
  let b := 𝒰.f k
  let B := baseChange b
  let : LocallyOfFinitePresentation (B.obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom b)
    infer_instance
  exact normalizer_range_locallyOfFinitePresentation_of_diagonalizable
    (B.map i) (hi.baseChange b) (h𝒰 k) (B.map n) hn'

/-- A closed relative-torus normalizer with locally finitely presented inclusion
and structure morphism, over an arbitrary base. -/
def relativeTorusFinitelyPresentedNormalizerModel
    {S : Scheme.{u}} {G : GroupScheme S} [LocallyOfFinitePresentation G.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) :
    {N : SubgroupFunctor.ClosedRepresentative (torusNormalizer t) //
      LocallyOfFinitePresentation N.hom.hom.hom.left ∧
        LocallyOfFinitePresentation N.group.X.hom} := by
  let N := relativeTorusClosedNormalizerModel t hT ht
  let hN : LocallyOfFinitePresentation N.hom.hom.hom.left :=
    normalizer_range_locallyOfFinitePresentation_of_multiplicativeType
      t ht hT.isMultiplicativeType N.hom N.represents
  refine ⟨N, hN, ?_⟩
  rw [← Over.w N.hom.hom.hom]
  infer_instance

end Langlands.GroupScheme
