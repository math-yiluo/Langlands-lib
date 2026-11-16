import Langlands.GroupScheme.Torus.DiagonalizableNormalizer
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.SubgroupFunctor.ClosedCoverDescent
import Langlands.GroupScheme.SubgroupFunctor.FppfLocality
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange

/-! # Closed normalizers of subgroups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Normalization of a represented subgroup is detected by an fppf cover of
the base, on all relative tests. -/
theorem normalizer_range_eq_coverDescent
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (i : H ⟶ G) [Mono i.hom.hom] :
    (range i).normalizer = CoverDescent.subgroup 𝒰
      (fun k => ((range i).normalizer).baseChange (𝒰.f k)) := by
  apply le_antisymm
  · intro U g hg k V a
    rw [mem_baseChange, MulEquiv.apply_symm_apply]
    exact (range i).normalizer.comp_mem a hg
  · intro U g hg V a x hx
    have hlocal (k : 𝒰.I₀) :
        fppfCoverMap (𝒰.pullback₁ V.hom) k ≫ ((a ≫ g) * x * (a ≫ g)⁻¹) ∈
            (range i).carrier (fppfCoverObj (𝒰.pullback₁ V.hom) k) ∧
        fppfCoverMap (𝒰.pullback₁ V.hom) k ≫ ((a ≫ g)⁻¹ * x * (a ≫ g)) ∈
            (range i).carrier (fppfCoverObj (𝒰.pullback₁ V.hom) k) := by
      let W : Over (𝒰.X k) := Over.mk (pullback.snd V.hom (𝒰.f k))
      let q : (Over.map (𝒰.f k)).obj W ⟶ V :=
        Over.homMk (pullback.fst V.hom (𝒰.f k)) pullback.condition
      have hm := hg k W (q ≫ a)
      rw [mem_baseChange, MulEquiv.apply_symm_apply] at hm
      have hc := hm _ (𝟙 _) (q ≫ x) ((range i).comp_mem q hx)
      simp only [Category.id_comp] at hc
      let r : fppfCoverObj (𝒰.pullback₁ V.hom) k ⟶ (Over.map (𝒰.f k)).obj W :=
        Over.homMk (𝟙 _) (by
          change 𝟙 _ ≫ (pullback.snd V.hom (𝒰.f k) ≫ 𝒰.f k) =
            pullback.fst V.hom (𝒰.f k) ≫ V.hom
          simpa only [Category.id_comp] using
            (pullback.condition (f := V.hom) (g := 𝒰.f k)).symm)
      have hr : r ≫ q = fppfCoverMap (𝒰.pullback₁ V.hom) k :=
        Over.OverMorphism.ext (Category.id_comp _)
      constructor
      · simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
          ← Category.assoc r q, hr] using (range i).comp_mem r hc.1
      · simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
          ← Category.assoc r q, hr] using (range i).comp_mem r hc.2
    exact ⟨(mem_range_iff_fppfCover i (𝒰.pullback₁ V.hom) _).mpr
        (fun k => (hlocal k).1),
      (mem_range_iff_fppfCover i (𝒰.pullback₁ V.hom) _).mpr
        (fun k => (hlocal k).2)⟩

/-- Closed representability of the full normalizer descends along any fppf
cover, provided the original subgroup is represented monomorphically. -/
theorem normalizer_range_isClosedRepresentable_of_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (i : H ⟶ G) [Mono i.hom.hom]
    (hc : ∀ k, (((range i).normalizer).baseChange (𝒰.f k)).IsClosedRepresentable) :
    (range i).normalizer.IsClosedRepresentable := by
  rw [normalizer_range_eq_coverDescent 𝒰 i]
  apply CoverDescent.isClosedRepresentable_subgroup_fppf 𝒰 _ ?_ hc
  intro k l V W a x hx
  rw [mem_baseChange, MulEquiv.apply_symm_apply]
  exact (range i).normalizer.comp_mem a hx

end SubgroupFunctor

open RelativeMultiplicativeType

/-- A diagonalizable subgroup over an affine base is compared with the
ring-level diagonalizable group before applying projective coordinates. -/
theorem diagonalizableNormalizer_hasClosedRepresentative_overSpec
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffine G.X.left] (i : H ⟶ G) (hH : IsDiagonalizable H)
    (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.HasClosedRepresentative := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let e' : H ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  have hi' : IsClosedSubgroup (e'.inv ≫ i) := by
    let : IsClosedImmersion i.hom.hom.left := hi
    change IsClosedImmersion (e'.inv.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have h := diagonalizableNormalizer_hasClosedRepresentative_overRing (e'.inv ≫ i) hi'
  change (SubgroupFunctor.range (e'.symm.hom ≫ i)).normalizer.HasClosedRepresentative at h
  rwa [SubgroupFunctor.range_iso_comp e'.symm i] at h

/-- Closed normalizers of diagonalizable subgroups over arbitrary bases.
No smoothness assumption on the subgroup or ambient group is needed. -/
theorem diagonalizableNormalizer_hasClosedRepresentative
    {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : IsDiagonalizable H) (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.HasClosedRepresentative := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hc : (SubgroupFunctor.range i).normalizer.IsClosedRepresentable := by
    apply SubgroupFunctor.normalizer_range_isClosedRepresentable_of_fppfCover 𝒰 i
    intro k
    let b := S.affineOpenCover.f k
    let B := GroupScheme.baseChange b
    let : IsAffineHom (B.obj G).X.hom :=
      MorphismProperty.pullback_snd G.X.hom b inferInstance
    let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
    change (((SubgroupFunctor.range i).normalizer).baseChange b).IsClosedRepresentable
    rw [SubgroupFunctor.normalizer_baseChange,
      ← SubgroupFunctor.range_baseChangeHom]
    obtain ⟨N, n, hn, hrep⟩ :=
      diagonalizableNormalizer_hasClosedRepresentative_overSpec
        (R := S.affineOpenCover.X k) (B.map i) (hH.baseChange b) (hi.baseChange b)
    exact ⟨N, n, hrep, hn⟩
  obtain ⟨N, n, hrep, hn⟩ := hc
  exact ⟨N, n, hn, hrep⟩

/-- A closed subgroup of multiplicative type in a relatively affine group
has an actual closed representative for its full normalizer. -/
theorem relativeMultiplicativeTypeNormalizer_hasClosedRepresentative
    {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : IsMultiplicativeType H) (hi : IsClosedSubgroup i) :
    (SubgroupFunctor.range i).normalizer.HasClosedRepresentative := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hc : (SubgroupFunctor.range i).normalizer.IsClosedRepresentable := by
    apply SubgroupFunctor.normalizer_range_isClosedRepresentable_of_fppfCover 𝒰 i
    intro k
    let b := 𝒰.f k
    let B := GroupScheme.baseChange b
    let : IsAffineHom (B.obj G).X.hom :=
      MorphismProperty.pullback_snd G.X.hom b inferInstance
    rw [SubgroupFunctor.normalizer_baseChange,
      ← SubgroupFunctor.range_baseChangeHom]
    obtain ⟨N, n, hn, hrep⟩ := diagonalizableNormalizer_hasClosedRepresentative
      (B.map i) (h𝒰 k) (hi.baseChange b)
    exact ⟨N, n, hrep, hn⟩
  obtain ⟨N, n, hrep, hn⟩ := hc
  exact ⟨N, n, hn, hrep⟩

namespace RelativeMultiplicativeType

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom]
  (i : H ⟶ G) (hH : IsMultiplicativeType H) (hi : IsClosedSubgroup i)

/-- A chosen closed group scheme representing the normalizer. -/
def normalizerGroupScheme : GroupScheme S :=
  (relativeMultiplicativeTypeNormalizer_hasClosedRepresentative i hH hi).choose

/-- The inclusion of the chosen normalizer into its ambient group. -/
def normalizerHom : normalizerGroupScheme i hH hi ⟶ G :=
  (relativeMultiplicativeTypeNormalizer_hasClosedRepresentative i hH hi).choose_spec.choose

/-- The chosen inclusion is closed and represents normalization on every test. -/
theorem normalizerHom_spec :
    IsClosedSubgroup (normalizerHom i hH hi) ∧
      (SubgroupFunctor.range i).normalizer.IsRepresentedBy (normalizerHom i hH hi) :=
  (relativeMultiplicativeTypeNormalizer_hasClosedRepresentative i hH hi).choose_spec.choose_spec

end RelativeMultiplicativeType

end Langlands.GroupScheme
