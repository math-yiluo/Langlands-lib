import Langlands.GroupScheme.Reductive.MonomorphismValuativeReduction
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Discrete valuation reduction for reductive group monomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace ReductiveMonomorphismValuativeReduction

/-- A finite-type monomorphism over a noetherian affine target is closed when all
its discrete valuation squares lift. -/
theorem isClosedImmersion_spec_of_dvr_lifts
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Mono f] [QuasiCompact f] [LocallyOfFiniteType f]
    (h : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → sq.commSq.HasLift) :
    IsClosedImmersion f := by
  have : UniversallyClosed f :=
    Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift f h
  have : IsProper f := { }
  exact (IsClosedImmersion.iff_isProper_and_mono f).mpr ⟨inferInstance, inferInstance⟩

/-- The same criterion over any locally noetherian target. -/
theorem isClosedImmersion_of_dvr_lifts
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Mono f] [QuasiCompact f] [LocallyOfFiniteType f]
    (h : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → sq.commSq.HasLift) :
    IsClosedImmersion f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    Y.affineOpenCover.openCover
  intro i
  let : IsOpenImmersion (Y.affineOpenCover.f i) := Y.affineOpenCover.map_prop i
  have : IsLocallyNoetherian (Spec (Y.affineOpenCover.X i)) :=
    isLocallyNoetherian_of_isOpenImmersion (Y.affineOpenCover.f i)
  have : IsNoetherianRing (Y.affineOpenCover.X i) := isLocallyNoetherian_Spec.mp inferInstance
  change IsClosedImmersion (pullback.snd f (Y.affineOpenCover.f i))
  exact isClosedImmersion_spec_of_dvr_lifts (R := Y.affineOpenCover.X i) _
    (Langlands.AlgebraicGeometry.NoetherianValuativeCriterion.hasLift_baseChange
      (IsPullback.of_hasPullback f (Y.affineOpenCover.f i)) h)

/-- A square for the underlying homomorphism lifts when its base-changed group
homomorphism over the valuation ring is a closed immersion. -/
theorem hasLift_of_baseChange_isClosedImmersion
    {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
    (sq : ValuativeCommSq f.hom.hom.left)
    (hc : IsClosedImmersion ((baseChange (sq.i₂ ≫ H.X.hom)).map f).hom.hom.left) :
    sq.commSq.HasLift := by
  let b := sq.i₂ ≫ H.X.hom
  let fR := ((baseChange b).map f).hom.hom.left
  have : IsClosedImmersion fR := hc
  let tR : Spec (CommRingCat.of sq.R) ⟶ ((baseChange b).obj H).X.left :=
    pullback.lift sq.i₂ (𝟙 _) (by simp [b])
  let tK : Spec (CommRingCat.of sq.K) ⟶ ((baseChange b).obj G).X.left :=
    pullback.lift sq.i₁ (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) (by
      rw [← Over.w f.hom.hom, ← Category.assoc, sq.commSq.w]
      rfl)
  let sqR : ValuativeCommSq fR :=
    { R := sq.R
      K := sq.K
      i₁ := tK
      i₂ := tR
      commSq := ⟨by
        apply pullback.hom_ext
        · change (tK ≫ ((Over.pullback b).map f.hom.hom).left) ≫ _ =
            (_ ≫ tR) ≫ _
          simp only [Category.assoc, tK, tR, Over.pullback_map_left,
            pullback.lift_fst_assoc, pullback.lift_fst]
          exact sq.commSq.w
        · change (tK ≫ ((Over.pullback b).map f.hom.hom).left) ≫ _ =
            (_ ≫ tR) ≫ _
          simp only [Category.assoc, tK, tR, Over.pullback_map_left,
            pullback.lift_snd, Category.comp_id]⟩ }
  have hex : ValuativeCriterion.Existence fR := by
    have hproper : IsProper fR := inferInstance
    exact (IsProper.eq_valuativeCriterion ▸ hproper).1.1.1.existence
  obtain ⟨l, hl₁, hl₂⟩ := (hex sqR).exists_lift
  refine ⟨⟨⟨l ≫ pullback.fst G.X.hom b, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, hl₁]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, ← (baseChange_map_isPullback b f).w, ← Category.assoc, hl₂]
    exact pullback.lift_fst _ _ _

/-- The DVR assertion implies the assertion over every locally noetherian base. -/
theorem locallyNoetherianCase_of_dvrCase (h : DvrCase.{u}) : LocallyNoetherianCase.{u} := by
  intro S _ G H hG hsep hfp hqc f hf
  let : IsSeparated H.X.hom := hsep
  let : LocallyOfFinitePresentation H.X.hom := hfp
  let : QuasiCompact H.X.hom := hqc
  let : Mono f.hom.hom.left := hf
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp _ H.X.hom
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ H.X.hom
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  apply isClosedImmersion_of_dvr_lifts f.hom.hom.left
  intro sq hsq
  let : IsDiscreteValuationRing sq.R := hsq
  let b := sq.i₂ ≫ H.X.hom
  have hmono : Mono ((baseChange b).map f).hom.hom.left :=
    (baseChange_map_isPullback b f).flip.mono_snd_of_mono
  apply hasLift_of_baseChange_isClosedImmersion f sq
  exact h sq.R ((baseChange b).obj G) ((baseChange b).obj H) (hG.baseChange b)
    (by change IsSeparated (pullback.snd H.X.hom b); infer_instance)
    (by change LocallyOfFinitePresentation (pullback.snd H.X.hom b); infer_instance)
    (by change QuasiCompact (pullback.snd H.X.hom b); infer_instance) _ hmono

end ReductiveMonomorphismValuativeReduction

end Langlands.GroupScheme
