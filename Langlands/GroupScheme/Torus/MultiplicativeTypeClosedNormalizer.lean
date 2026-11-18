import Langlands.GroupScheme.Absolute.ConjugationIntoLocus
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizer
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType
import Langlands.GroupScheme.Torus.SeparatedCentralizerModel

/-! # Closed normalizers of multiplicative-type subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S}

private theorem mem_normalizer_iff_holds (i : H ⟶ G) {U : Over S} (g : U ⟶ G.X) :
    g ∈ (range i).normalizer.carrier U ↔
      ConjugationInto.Holds i i g ∧ ConjugationInto.Holds i i g⁻¹ := by
  rw [mem_normalizer]
  constructor
  · intro h
    exact ⟨fun V a x => (h V a _ (mem_range.mpr ⟨x, rfl⟩)).2,
      fun V a x => by
        simpa only [GrpObj.comp_inv, inv_inv] using
          (h V a _ (mem_range.mpr ⟨x, rfl⟩)).1⟩
  · rintro ⟨h, hinv⟩ V a z hz
    obtain ⟨x, rfl⟩ := mem_range.mp hz
    exact ⟨by simpa only [GrpObj.comp_inv, inv_inv] using hinv V a x, h V a x⟩

/-- For a closed subgroup over an affine base with affine, flat structure and
fpqc-projective coordinates, its full normalizer is a closed subgroup scheme. -/
theorem normalizer_range_isClosedRepresentable_overRing {R : CommRingCat.{u}}
    {H G : GroupScheme (Spec R)} [IsAffineHom H.X.hom] [Flat H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hcoords : HasFpqcProjectiveCoordinateModule H) :
    (range i).normalizer.IsClosedRepresentable := by
  obtain ⟨Z, j, hj, hZ⟩ :=
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus
      R H.X inferInstance inferInstance hcoords G.X (ConjugationInto.productLocus i i)
      (ConjugationInto.productInclusion i i) (ConjugationInto.productInclusion_isClosedImmersion i i hi)
  have hfactor (U : Over (Spec R)) (g : U ⟶ G.X) :
      (∃ z : U ⟶ Z, z ≫ j = g) ↔ ConjugationInto.Holds i i g :=
    (hZ U g).trans (ConjugationInto.holds_iff_factors i i g).symm
  let invG := GrpObj.inv (X := G.X)
  let j' := j ≫ invG
  let n : pullback j j' ⟶ G.X := pullback.fst j j' ≫ j
  let : IsClosedImmersion j.left := hj
  have : IsIso invG.left := ((Over.forget _).mapIso (asIso invG)).isIso_hom
  have hj' : IsClosedImmersion j'.left := by
    change IsClosedImmersion (j.left ≫ invG.left)
    infer_instance
  have : IsClosedImmersion (pullback.fst j j').left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback j j').map (Over.forget _)).flip) hj'
  have : IsClosedImmersion n.left := by
    change IsClosedImmersion ((pullback.fst j j').left ≫ j.left)
    infer_instance
  have : Mono n := Over.mono_of_mono_left n
  apply (range i).normalizer.isClosedRepresentable_of_scheme n
  intro U g
  rw [mem_normalizer_iff_holds, ← hfactor, ← hfactor]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hab : a ≫ j = b ≫ j' := by
      rw [show j' = j ≫ invG from rfl, ← Category.assoc, hb, ha]
      exact (inv_inv g).symm
    exact ⟨pullback.lift a b hab, by simp only [n, pullback.lift_fst_assoc, ha]⟩
  · rintro ⟨y, hy⟩
    refine ⟨⟨y ≫ pullback.fst j j', by simpa only [Category.assoc] using hy⟩,
      ⟨y ≫ pullback.snd j j', ?_⟩⟩
    have heq : ((y ≫ pullback.snd j j') ≫ j) ≫ invG = g := by
      rw [Category.assoc, Category.assoc, ← show j' = j ≫ invG from rfl,
        ← pullback.condition, ← Category.assoc]
      exact hy
    have h := congrArg (fun p : U ⟶ G.X => p⁻¹) heq
    change (((y ≫ pullback.snd j j') ≫ j)⁻¹)⁻¹ = g⁻¹ at h
    simpa only [inv_inv] using h

end SubgroupFunctor

open RelativeMultiplicativeType in
private theorem normalizer_range_isClosedRepresentable_of_diagonalizable_overRing
    {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    (i : H ⟶ G) (hH : IsDiagonalizable H) (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.IsClosedRepresentable := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  let e' : H ≅ (Diagonalizable.groupScheme R Λ).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) Λ
  let : Flat (Diagonalizable.groupScheme R Λ).toGrp.X.hom :=
    Diagonalizable.flat_structure R Λ
  have h := SubgroupFunctor.normalizer_range_isClosedRepresentable_overRing
    (e'.inv ≫ i) (IsClosedSubgroup.iso_comp e'.symm hi)
    (Diagonalizable.hasFpqcProjectiveCoordinateModule R Λ)
  change (SubgroupFunctor.range (e'.symm.hom ≫ i)).normalizer.IsClosedRepresentable at h
  rwa [SubgroupFunctor.range_iso_comp e'.symm i] at h

private theorem normalizer_range_isClosedRepresentable_of_diagonalizable
    {S : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsDiagonalizable H) (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.IsClosedRepresentable := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.normalizer_range_isClosedRepresentable_of_fppfCover 𝒰 i
  intro k
  let b := S.affineOpenCover.f k
  change (((SubgroupFunctor.range i).normalizer).baseChange b).IsClosedRepresentable
  rw [SubgroupFunctor.normalizer_baseChange, ← SubgroupFunctor.range_baseChangeHom]
  exact normalizer_range_isClosedRepresentable_of_diagonalizable_overRing
    ((baseChange b).map i) (hH.baseChange b) (hi.baseChange b)

/-- A closed multiplicative-type subgroup has a closed all-test normalizer in
any ambient group scheme. -/
theorem normalizer_range_isClosedRepresentable_of_multiplicativeType
    {S : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.IsClosedRepresentable := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.normalizer_range_isClosedRepresentable_of_fppfCover 𝒰 i
  intro k
  rw [SubgroupFunctor.normalizer_baseChange, ← SubgroupFunctor.range_baseChangeHom]
  exact normalizer_range_isClosedRepresentable_of_diagonalizable
    ((baseChange (𝒰.f k)).map i) (h𝒰 k) (hi.baseChange (𝒰.f k))

/-- The actual closed normalizer of a closed relative torus in any ambient
group scheme over the same base. -/
def relativeTorusClosedNormalizerModel {S : Scheme.{u}} {G : GroupScheme S}
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) : SubgroupFunctor.ClosedRepresentative (torusNormalizer t) :=
  SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable
    (normalizer_range_isClosedRepresentable_of_multiplicativeType t hT.isMultiplicativeType ht)

end Langlands.GroupScheme
