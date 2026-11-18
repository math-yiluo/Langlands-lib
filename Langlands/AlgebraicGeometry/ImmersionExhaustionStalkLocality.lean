import Langlands.AlgebraicGeometry.ImmersionExhaustionFamilies
import Langlands.AlgebraicGeometry.IsomorphismLocalizationSpreading
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk

/-! # Spreading fullness from base stalks -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.IsomorphismLocalization

/-- A morphism between finitely presented relative schemes that is invertible
over a base stalk is invertible after restriction along an open neighborhood. -/
def OpenSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y) (s : S),
    IsIso ((Over.pullback (S.fromSpecStalk s)).map f) →
    ∃ (T : Scheme.{u}) (b : T ⟶ S), IsOpenImmersion b ∧ s ∈ Set.range b ∧
      IsIso ((Over.pullback b).map f)

theorem openSpreading : OpenSpreadingStatement.{u} := by
  intro S X Y _ _ _ _ _ _ f s hsIso
  obtain ⟨_, ⟨U, hUmem, rfl⟩, hs, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hU : IsAffineOpen U := hUmem
  let R := Γ(S, U)
  let L := S.presheaf.stalk s
  let P := (hU.primeIdealOf ⟨s, hs⟩).asIdeal
  let a := hU.fromSpec
  let : Algebra R L := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨s, hs⟩
  let : P.IsPrime := (hU.primeIdealOf ⟨s, hs⟩).isPrime
  let : IsLocalization.AtPrime L P := hU.isLocalization_stalk ⟨s, hs⟩
  have hstalk : Spec.algebraMap R L ≫ a = S.fromSpecStalk s :=
    hU.fromSpecStalk_eq_fromSpecStalk hs
  let X' := (Over.pullback a).obj X
  let Y' := (Over.pullback a).obj Y
  let f' : X' ⟶ Y' := (Over.pullback a).map f
  let : LocallyOfFinitePresentation X'.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom a))
  let : QuasiCompact X'.hom := inferInstanceAs (QuasiCompact (pullback.snd X.hom a))
  let : QuasiSeparated X'.hom := inferInstanceAs (QuasiSeparated (pullback.snd X.hom a))
  let : LocallyOfFinitePresentation Y'.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y.hom a))
  let : QuasiCompact Y'.hom := inferInstanceAs (QuasiCompact (pullback.snd Y.hom a))
  let : QuasiSeparated Y'.hom := inferInstanceAs (QuasiSeparated (pullback.snd Y.hom a))
  have hprime : IsIso ((Over.pullback (Spec.algebraMap R L)).map f') :=
    (NatIso.isIso_map_iff (Over.pullbackComp (Spec.algebraMap R L) a) f).mp
      (Eq.mpr (congrArg (fun (b : Spec L ⟶ S) => IsIso ((Over.pullback b).map f)) hstalk) hsIso)
  have hprimeLeft : IsIso (((Over.pullback (Spec.algebraMap R L)).map f').left) :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mpr hprime
  obtain ⟨g, hg, hiso⟩ := exists_away_isIso_of_atPrime P L f' hprimeLeft
  let d := Spec.algebraMap R (Localization.Away g)
  let : IsOpenImmersion d := Scheme.isOpenImmersion_SpecMap_localizationAway (R := R) g
  have hmem : hU.primeIdealOf ⟨s, hs⟩ ∈ d.opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway (R := R) g]
    exact hg
  obtain ⟨t, ht⟩ := hmem
  refine ⟨_, d ≫ a, inferInstance, ⟨t, ?_⟩, ?_⟩
  · rw [Scheme.Hom.comp_apply, ht]
    exact hU.fromSpec_primeIdealOf ⟨s, hs⟩
  · exact (NatIso.isIso_map_iff (Over.pullbackComp d a) f).mpr
      ((isIso_iff_of_reflects_iso _ (Over.forget _)).mp hiso)

end Langlands.AlgebraicGeometry.IsomorphismLocalization

namespace Langlands.AlgebraicGeometry.ImmersionExhaustion.Family

/-- For a quasi-compact finite-type ambient morphism over a noetherian base,
fullness over each base stalk implies fullness at one global stage. -/
theorem full_of_stalk_full {S : Scheme.{u}} [IsNoetherian S]
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Family S I) (hft : LocallyOfFiniteType D.ambient.hom)
    (hqc : QuasiCompact D.ambient.hom)
    (h : ∀ s : S, (D.baseChange (S.fromSpecStalk s)).Full) : D.Full := by
  let := hft
  let := hqc
  let : IsNoetherian D.ambient.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian D.ambient.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace D.ambient.hom }
  apply D.full_of_pointwise_open
  intro x
  obtain ⟨i, hi⟩ := h (D.ambient.hom x)
  let : IsImmersion (D.inclusion i).left := D.immersion i
  let : LocallyOfFiniteType (D.member i).hom := by
    rw [← Over.w (D.inclusion i)]
    infer_instance
  let : IsLocallyNoetherian (D.member i).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.member i).hom
  let : NoetherianSpace (D.member i).left :=
    (D.inclusion i).left.isEmbedding.isInducing.noetherianSpace
  obtain ⟨T, b, hb, hx, hiso⟩ := IsomorphismLocalization.openSpreading S
    (D.member i) D.ambient (D.inclusion i) (D.ambient.hom x) hi
  let := hb
  let p := pullback.fst D.ambient.hom b
  have hx' : x ∈ p.opensRange := by
    change x ∈ Set.range p
    rw [IsOpenImmersion.range_pullbackFst b D.ambient.hom]
    exact hx
  refine ⟨p.opensRange, hx', i, ?_⟩
  let j := (D.inclusion i).left
  let : IsIso (pullback.snd j p) := (isIso_over_map_iff (D.inclusion i) b).mp hiso
  let e := p.isoOpensRange
  have hpb : IsPullback (pullback.fst j p) (pullback.snd j p ≫ e.hom)
      j p.opensRange.ι :=
    (IsPullback.of_hasPullback j p).of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [e])
  exact IsIso.of_isIso_fac_left hpb.isoPullback_hom_snd

end Langlands.AlgebraicGeometry.ImmersionExhaustion.Family
