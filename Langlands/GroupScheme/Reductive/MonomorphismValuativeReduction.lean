import Langlands.GroupScheme.Reductive.MonomorphismValuativeReductionStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion

/-! # The DVR valuative reduction for reductive group monomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace ReductiveMonomorphismValuativeReduction

variable {S : Scheme.{u}} {G H : GroupScheme S}
    (hG : IsReductive G) [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom.left]

include hG in
/-- The DVR case gives a lift of every actual DVR valuative square, over any base. -/
theorem hasLift_of_dvrCase (hDvr : DvrCase.{u})
    (sq : ValuativeCommSq f.hom.hom.left) [IsDiscreteValuationRing sq.R] :
    sq.commSq.HasLift := by
  let b := sq.i₂ ≫ H.X.hom
  let Gb := (baseChange b).obj G
  let Hb := (baseChange b).obj H
  let fb := (baseChange b).map f
  have : IsSeparated Hb.X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation Hb.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd H.X.hom b)
    infer_instance
  have : QuasiCompact Hb.X.hom := by
    change QuasiCompact (pullback.snd H.X.hom b)
    infer_instance
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have : Mono fb.hom.hom.left := by
    change Mono ((Over.pullback b).map f.hom.hom).left
    infer_instance
  have : IsClosedImmersion fb.hom.hom.left :=
    hDvr sq.R Gb Hb (hG.baseChange b) inferInstance inferInstance inferInstance fb inferInstance
  let a := Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
  let i₁ : Spec (CommRingCat.of sq.K) ⟶ Gb.X.left :=
    pullback.lift sq.i₁ a (by
      dsimp [b, a]
      rw [← Category.assoc, ← sq.commSq.w, Category.assoc, Over.w f.hom.hom])
  let i₂ : Spec (CommRingCat.of sq.R) ⟶ Hb.X.left :=
    pullback.lift sq.i₂ (𝟙 _) (by simp [b])
  let sqb : ValuativeCommSq fb.hom.hom.left :=
    { R := sq.R
      K := sq.K
      i₁ := i₁
      i₂ := i₂
      commSq := ⟨by
        apply pullback.hom_ext
        · simpa [i₁, i₂, fb, Over.pullback_map_left, a] using sq.commSq.w
        · simp [i₁, i₂, fb, Over.pullback_map_left, a]⟩ }
  have hVC : ValuativeCriterion.Existence fb.hom.hom.left := by
    have hv : (ValuativeCriterion.Existence ⊓ @QuasiCompact) fb.hom.hom.left := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact hv.1
  obtain ⟨l, hl₁, hl₂⟩ := (hVC sqb).exists_lift
  refine ⟨⟨⟨l ≫ pullback.fst G.X.hom b, ?_, ?_⟩⟩⟩
  · simpa [sqb, i₁, Category.assoc] using
      congrArg (fun t => t ≫ pullback.fst G.X.hom b) hl₁
  · have hw : fb.hom.hom.left ≫ pullback.fst H.X.hom b =
        pullback.fst G.X.hom b ≫ f.hom.hom.left := by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp [Over.pullback_map_left]
    rw [Category.assoc, ← hw, ← Category.assoc, hl₂]
    simp [sqb, i₂]

/-- An actual lift, including its two factorization equations, chosen from the DVR case. -/
def dvrValuativeLift (hDvr : DvrCase.{u})
    (sq : ValuativeCommSq f.hom.hom.left) [IsDiscreteValuationRing sq.R] :
    sq.commSq.LiftStruct :=
  (hasLift_of_dvrCase hG f hDvr sq).exists_lift.some

include hG in
/-- Over a locally noetherian base, the DVR case makes the given monomorphism closed. -/
theorem isClosedImmersion_of_dvrCase [IsLocallyNoetherian S] (hDvr : DvrCase.{u}) :
    IsClosedImmersion f.hom.hom.left := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp f.hom.hom.left H.X.hom
  have : IsAffineHom (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : IsAffineHom f.hom.hom.left := IsAffineHom.of_comp _ H.X.hom
  have : IsLocallyNoetherian H.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have hLifts : ∀ sq : ValuativeCommSq f.hom.hom.left,
      IsDiscreteValuationRing sq.R → sq.commSq.HasLift := by
    intro sq hsq
    let := hsq
    exact hasLift_of_dvrCase hG f hDvr sq
  have : UniversallyClosed f.hom.hom.left := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @UniversallyClosed)
      H.X.left.affineOpenCover.openCover
    intro i
    let c := H.X.left.affineOpenCover.f i
    let g := pullback.snd f.hom.hom.left c
    have hN : IsLocallyNoetherian (Spec (H.X.left.affineOpenCover.X i)) :=
      isLocallyNoetherian_of_isOpenImmersion c
    have : IsNoetherianRing (H.X.left.affineOpenCover.X i) :=
      isLocallyNoetherian_Spec.mp hN
    change UniversallyClosed g
    apply Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift
      (R := H.X.left.affineOpenCover.X i) g
    exact fun sq hsq =>
      Langlands.AlgebraicGeometry.NoetherianValuativeCriterion.hasLift_baseChange
        (IsPullback.of_hasPullback f.hom.hom.left c) hLifts sq hsq
  have : IsProper f.hom.hom.left := {}
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end ReductiveMonomorphismValuativeReduction

/-- The exact published noetherian/DVR reduction. -/
theorem reductiveMonomorphismValuativeReduction :
    ReductiveMonomorphismValuativeReductionStatement.{u} := by
  constructor
  · intro hDvr S _ G H hG _ _ _ f _
    exact ReductiveMonomorphismValuativeReduction.isClosedImmersion_of_dvrCase hG f hDvr
  · intro hNoeth R _ _ _ G H hG hsep hfp hqc f hmono
    exact hNoeth (Spec (CommRingCat.of R)) G H hG hsep hfp hqc f hmono

end Langlands.GroupScheme
