import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFiniteTypePullbacks
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartCover
import Langlands.Geometry.Analytic.SpaceAnalytificationFibreProductStatement
import Langlands.Geometry.Analytic.SpaceAnalytificationLocalLifts

/-! # Analytification preserves fibre products of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

private theorem separated_of_pullback
    {S : Scheme.{u}} {W X₁ X₂ Z : AlgebraicSpace S}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂) (h₁ : IsSeparated X₁) (h₂ : IsSeparated X₂) :
    IsSeparated W := by
  let P : MorphismProperty Scheme.{u} := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}
  let Q := P.inverseImage (Over.forget S)
  let R := Q.relative (schemeYoneda S)
  let : Q.IsMultiplicative := inferInstance
  let : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let : R.IsMultiplicative :=
    MorphismProperty.relative_isMultiplicative (P := Q) (F := schemeYoneda S)
  have hp : R (diag (Limits.pullback (hom f₁) (hom f₂))) :=
    PullbackDiagonals.pullback R (hom f₁) (hom f₂) h₁ h₂
  exact relative_diag_of_iso P (hw.map (forgetToPresheaf S)).isoPullback.symm hp

private theorem locallyOfFiniteType_of_pullback
    {S : Scheme.{u}} {W X₁ X₂ Z : AlgebraicSpace S}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂) (hZ : IsSeparated Z)
    (h₁ : LocallyOfFiniteTypeOverBase X₁) (h₂ : LocallyOfFiniteTypeOverBase X₂) :
    LocallyOfFiniteTypeOverBase W := by
  let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition
  let : MorphismProperty.RespectsIso (@Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange.respectsIso
  let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition
  obtain ⟨U, a, hae, has, hU⟩ := h₁.exists_atlas
  obtain ⟨V, b, hbe, hbs, hV⟩ := h₂.exists_atlas
  let : LocallyOfFiniteType U.hom := hU
  let : LocallyOfFiniteType V.hom := hV
  let h := Z.representable_from_scheme (a ≫ hom f₁)
  let e := FibreProduct.presheafIso f₁ f₂
  have hA : LocallyOfFiniteType (FibreProduct.atlasScheme (f := f₁) (g := f₂) a b).hom :=
    locallyOfFiniteType_of_isPullback_of_closedDiagonal hZ (a ≫ hom f₁) (b ≫ hom f₂)
      (h.fst' (b ≫ hom f₂)) (h.snd (b ≫ hom f₂)) (h.isPullback' (b ≫ hom f₂))
  have hft : LocallyOfFiniteTypeOverBase (fibreProduct f₁ f₂) :=
    ⟨_, FibreProduct.atlasMap a b ≫ e.inv,
      IsEtale.comp_iso (FibreProduct.relative_atlasMap (@Etale.{u}) hae hbe) e.symm,
      IsSurjective.comp_iso (FibreProduct.relative_atlasMap (@Surjective.{u}) has hbs) e.symm, hA⟩
  exact hft.of_iso ((forgetToPresheaf S).mapIso ((FibreProduct.isPullback f₁ f₂).isoIsPullback _ _ hw))

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K))}

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem ringPoint_ext_of_pullback
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂)
    {R : Type u} [CommRing R] [Algebra K R] {a b : RingPoints K W R}
    (h₁ : RingPoints.map π₁ a = RingPoints.map π₁ b)
    (h₂ : RingPoints.map π₂ a = RingPoints.map π₂ b) : a = b := by
  apply (uliftYonedaEquiv.{u + 1}).symm.injective
  change pointHom K a = pointHom K b
  apply (hw.map (forgetToPresheaf _)).hom_ext
  · exact (pointHom_map K π₁ a).symm.trans
      ((congrArg (pointHom K) h₁).trans (pointHom_map K π₁ b))
  · exact (pointHom_map K π₂ a).symm.trans
      ((congrArg (pointHom K) h₂).trans (pointHom_map K π₂ b))

set_option maxHeartbeats 1000000 in
/-- Analytification carries the given algebraic-space pullback to a
categorical pullback in the localized analytic category. -/
theorem spaceAnalytificationFibreProduct : SpaceAnalytificationFibreProductStatement.{u} := by
  classical
  intro K _ _ _ W X₁ X₂ Z π₁ π₂ f₁ f₂ hw hs₁ ht₁ hs₂ ht₂ hsZ htZ
    V Y₁ Y₂ T q p₁ p₂ r hq hp₁ hp₂ hr Φ₁ Φ₂ F₁ F₂ hπ₁ hπ₂ hf₁ hf₂
  have hsW := separated_of_pullback hw hs₁ hs₂
  have htW := locallyOfFiniteType_of_pullback hw hsZ ht₁ ht₂
  let wPoint := affinoidPointHom hq hsW htW
  let xPoint₁ := affinoidPointHom hp₁ hs₁ ht₁
  let xPoint₂ := affinoidPointHom hp₂ hs₂ ht₂
  let zPoint := affinoidPointHom hr hsZ htZ
  have hΦ₁ (R : PresentedAffinoidAlgebra K) (x : RingPoints K W R) :
      wPoint R x ≫ Φ₁ = xPoint₁ R (RingPoints.map π₁ x) :=
    affinoidPointHom_comp hq hsW htW hp₁ hs₁ ht₁ π₁ Φ₁ hπ₁ R x
  have hΦ₂ (R : PresentedAffinoidAlgebra K) (x : RingPoints K W R) :
      wPoint R x ≫ Φ₂ = xPoint₂ R (RingPoints.map π₂ x) :=
    affinoidPointHom_comp hq hsW htW hp₂ hs₂ ht₂ π₂ Φ₂ hπ₂ R x
  have hF₁ (R : PresentedAffinoidAlgebra K) (x : RingPoints K X₁ R) :
      xPoint₁ R x ≫ F₁ = zPoint R (RingPoints.map f₁ x) :=
    affinoidPointHom_comp hp₁ hs₁ ht₁ hr hsZ htZ f₁ F₁ hf₁ R x
  have hF₂ (R : PresentedAffinoidAlgebra K) (x : RingPoints K X₂ R) :
      xPoint₂ R x ≫ F₂ = zPoint R (RingPoints.map f₂ x) :=
    affinoidPointHom_comp hp₂ hs₂ ht₂ hr hsZ htZ f₂ F₂ hf₂ R x
  have hcomm : Φ₁ ≫ F₁ = Φ₂ ≫ F₂ := by
    apply etaleCoverHomExt (fun i : EtaleAffineTest K W => q i.algebra i.presentation i.point)
      (fun i => hq.etale_map i.presentation i.point i.etale_point)
    · intro y
      obtain ⟨A, _, _, P, x, hx, hy⟩ := hq.jointly_surjective y
      exact ⟨⟨CommAlgCat.of K A, P, x, hx⟩, hy⟩
    · intro i
      rw [← Category.assoc, hπ₁, hf₁, ← RingPoints.map_comp, hw.w,
        RingPoints.map_comp, ← hf₂, ← hπ₂, Category.assoc]
  have hmono (S : LocalizedCategory.{u, u, u} (K := K)) (l m : S ⟶ V)
      (he₁ : l ≫ Φ₁ = m ≫ Φ₁) (he₂ : l ≫ Φ₂ = m ≫ Φ₂) : l = m := by
    obtain ⟨S₀, hS⟩ := localizedObjectEquiv.surjective S
    change localizationFunctor.obj S₀ = S at hS
    subst S
    obtain ⟨A, e, I, hI, h⟩ := exists_affinoidPointHom_pair_chartCover
      hq hq hsW htW hsW htW S₀ l m
    apply (cancel_epi e.hom).mp
    apply localizedHom_ext_of_chartCover (fun i : I => i.val) hI
    intro i
    obtain ⟨a, b, ha, hb⟩ := h i
    change wPoint _ a = _ at ha
    change wPoint _ b = _ at hb
    let j : localizedAffinoidSpectrum (A.presentation.atlas.algebra i.val) ⟶
        localizationFunctor.obj S₀ := localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom
    have ha' : wPoint _ a = j ≫ l := ha.trans (Category.assoc _ _ _).symm
    have hb' : wPoint _ b = j ≫ m := hb.trans (Category.assoc _ _ _).symm
    have heq : a = b := by
      apply ringPoint_ext_of_pullback hw
      · apply affinoidPointHom_injective hp₁ hs₁ ht₁
        change xPoint₁ _ _ = xPoint₁ _ _
        rw [← hΦ₁ _ a, ← hΦ₁ _ b, ha', hb', Category.assoc j l Φ₁,
          Category.assoc j m Φ₁, he₁]
      · apply affinoidPointHom_injective hp₂ hs₂ ht₂
        change xPoint₂ _ _ = xPoint₂ _ _
        rw [← hΦ₂ _ a, ← hΦ₂ _ b, ha', hb', Category.assoc j l Φ₂,
          Category.assoc j m Φ₂, he₂]
    exact ha.symm.trans ((congrArg (wPoint _) heq).trans hb)
  have hLift (S : LocalizedCategory.{u, u, u} (K := K)) (a : S ⟶ Y₁) (b : S ⟶ Y₂)
      (hab : a ≫ F₁ = b ≫ F₂) : ∃ l : S ⟶ V, l ≫ Φ₁ = a ∧ l ≫ Φ₂ = b := by
    obtain ⟨S₀, hS₀⟩ := localizedObjectEquiv.surjective S
    change localizationFunctor.obj S₀ = S at hS₀
    subst S
    obtain ⟨A, e, I, hI, h⟩ := exists_affinoidPointHom_pair_chartCover
      hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ S₀ a b
    have hlocal (i : I) : ∃ l : localizationFunctor.obj (A.smallChartSpectrum i.val) ⟶ V,
        l ≫ Φ₁ = localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom ≫ a ∧
        l ≫ Φ₂ = localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom ≫ b := by
      obtain ⟨x₁, x₂, hx₁, hx₂⟩ := h i
      change xPoint₁ _ x₁ = _ at hx₁
      change xPoint₂ _ x₂ = _ at hx₂
      let j : localizedAffinoidSpectrum (A.presentation.atlas.algebra i.val) ⟶
          localizationFunctor.obj S₀ := localizationFunctor.map (A.smallChartSpectrumInclusion i.val) ≫ e.hom
      have hx₁' : xPoint₁ _ x₁ = j ≫ a := hx₁.trans (Category.assoc _ _ _).symm
      have hx₂' : xPoint₂ _ x₂ = j ≫ b := hx₂.trans (Category.assoc _ _ _).symm
      have hwx : RingPoints.map f₁ x₁ = RingPoints.map f₂ x₂ := by
        apply affinoidPointHom_injective hr hsZ htZ
        change zPoint _ _ = zPoint _ _
        rw [← hF₁ _ x₁, ← hF₂ _ x₂, hx₁', hx₂', Category.assoc j a F₁,
          Category.assoc j b F₂, hab]
      obtain ⟨x, h₁, h₂⟩ := exists_ringPoint_of_isPullback hw x₁ x₂ hwx
      exact ⟨wPoint _ x, (hΦ₁ _ x).trans ((congrArg (xPoint₁ _) h₁).trans hx₁),
        (hΦ₂ _ x).trans ((congrArg (xPoint₂ _) h₂).trans hx₂)⟩
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift_of_chartCover (fun i : I => i.val) hI Φ₁ Φ₂ hmono
      (e.hom ≫ a) (e.hom ≫ b) hlocal
    refine ⟨e.inv ≫ l, ?_, ?_⟩
    · rw [Category.assoc, hl₁, Iso.inv_hom_id_assoc]
    · rw [Category.assoc, hl₂, Iso.inv_hom_id_assoc]
  let hl (c : PullbackCone F₁ F₂) := hLift c.pt c.fst c.snd c.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm
    (fun c => Classical.choose (hl c))
    (fun c => (Classical.choose_spec (hl c)).1)
    (fun c => (Classical.choose_spec (hl c)).2)
    (fun c m hm₁ hm₂ => hmono c.pt m _
      (hm₁.trans (Classical.choose_spec (hl c)).1.symm)
      (hm₂.trans (Classical.choose_spec (hl c)).2.symm)))

end Langlands.Analytic.SpaceAnalytification
