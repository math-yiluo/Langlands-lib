import Langlands.Cohomology.Tate.CohomologyTransferZero
import Langlands.Cohomology.Tate.PositiveRestriction

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype (G ⧸ H)] in
/-- Restricted coinduced replacements have vanishing positive comparison homology. -/
lemma zeroSplice_restrictedCoinduced_isZero (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    IsZero ((zeroSpliceComplex (Rep.res H.subtype (coinduced A))).homology n) :=
  (restrictedCoinduced_tate_isZero H A n).of_iso
    ((zeroSpliceConnectData (Rep.res H.subtype (coinduced A))).homologyIsoPos n n rfl ≪≫
      ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype (coinduced A))).symm)

omit [Fintype G] [Fintype (G ⧸ H)] in
/-- The restricted embedding sequence supplies all positive comparison classes as boundaries. -/
lemma zeroSplice_restrictedShiftUp_delta_surjective (A : Rep.{u} R G) (n : ℕ) :
    Function.Surjective
      ((zeroSplice_shortExact (restrictedShiftUpSequence_shortExact H A)).δ
        n (n + 1) rfl) := by
  have := (zeroSplice_shortExact (restrictedShiftUpSequence_shortExact H A)).epi_δ
    n (n + 1) rfl (zeroSplice_restrictedCoinduced_isZero H A (n + 1))
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Tate corestriction agrees with the independently constructed transfer comparison. -/
lemma corestriction_cochainsToTate (A : Rep.{u} R G) (n : ℕ)
    (x : (zeroSpliceComplex (Rep.res H.subtype A)).homology n) :
    corestriction H A n
        (HomologicalComplex.homologyMap
          (cochainsToTate (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) n x) =
      HomologicalComplex.homologyMap (transferCochainsToTate H A) n x := by
  induction n generalizing A with
  | zero =>
    obtain ⟨a, rfl⟩ := (zeroSpliceZeroEquiv (Rep.res H.subtype A)).symm.toLinearEquiv.surjective x
    have hz := cochainsToTate_zero
      (A := Rep.res H.subtype A) (B := Rep.res H.subtype A)
      (MonoidHom.id H) (𝟙 (Rep.res H.subtype A)) a
    have ht := transferCochainsToTate_zero H A a
    have hc := corestrictionZero_zeroClass (A := A) H a
    exact (congrArg (corestrictionZero H A) hz).trans (hc.trans ht.symm)
  | succ n ih =>
    obtain ⟨y, rfl⟩ := zeroSplice_restrictedShiftUp_delta_surjective H A n x
    have hz := cochainsToTate_identity_delta
      ((shiftUpSequence A).map (Rep.resFunctor H.subtype))
      (restrictedShiftUpSequence_shortExact H A) n y
    have hc := corestriction_scalarSplit_delta H (shiftUpSequence A)
      (shiftUpSequence_scalarSplitting A) n
      (HomologicalComplex.homologyMap
        (cochainsToTate (A := Rep.res H.subtype (shiftUp A))
          (MonoidHom.id H) (𝟙 (Rep.res H.subtype (shiftUp A)))) n y)
    have hi := congrArg (TateCohomology.δ (shiftUpSequence_shortExact A) n)
      (ih (shiftUp A) y)
    have ht := ConcreteCategory.congr_hom
      (transferCochainsToTate_delta H (shiftUpSequence A)
        (shiftUpSequence_shortExact A) n) y
    exact (congrArg (corestriction H A (n + 1)) hz).trans (hc.trans (hi.trans ht.symm))

/-- In positive degrees Tate corestriction is ordinary cohomological corestriction. -/
theorem corestriction_groupCohomology (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    ModuleCat.ofHom (corestriction H A n) =
      ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)).hom ≫
        ordinaryCohomologyCorestriction H A n ≫
          ((TateCohomology.isoGroupCohomology n).app A).inv := by
  have hh :
      HomologicalComplex.homologyMap
          (cochainsToTate (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) n ≫
          ModuleCat.ofHom (corestriction H A n) =
        HomologicalComplex.homologyMap (transferCochainsToTate H A) n := by
    ext x
    exact corestriction_cochainsToTate H A n x
  rw [cochainsToTate_homology_id, transferCochainsToTate_homology] at hh
  apply (cancel_epi
    ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  exact (cancel_epi
    ((zeroSpliceConnectData (Rep.res H.subtype A)).homologyIsoPos n n rfl).hom).mp
      (by simpa only [Category.assoc] using hh)

end Langlands.Tate
