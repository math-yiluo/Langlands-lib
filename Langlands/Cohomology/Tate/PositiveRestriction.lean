import Langlands.Cohomology.Tate.CochainComparison
import Langlands.Cohomology.Tate.SplitTransfer

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Positive homology of the auxiliary splice of a coinduced replacement vanishes. -/
lemma zeroSplice_coinduced_isZero (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    IsZero ((zeroSpliceComplex (coinduced A)).homology n) :=
  (coinduced_tate_isZero A n).of_iso
    ((zeroSpliceConnectData (coinduced A)).homologyIsoPos n n rfl ≪≫
      ((TateCohomology.isoGroupCohomology n).app (coinduced A)).symm)

/-- Every positive-degree comparison class is a boundary of an embedding-shift class. -/
lemma zeroSplice_shiftUp_delta_surjective (A : Rep.{u} R G) (n : ℕ) :
    Function.Surjective
      ((zeroSplice_shortExact (shiftUpSequence_shortExact A)).δ n (n + 1) rfl) := by
  have := (zeroSplice_shortExact (shiftUpSequence_shortExact A)).epi_δ n (n + 1) rfl
    (zeroSplice_coinduced_isZero A (n + 1))
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

lemma cochainsToTate_identity_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) (x : (zeroSpliceComplex S.X₃).homology n) :
    HomologicalComplex.homologyMap (cochainsToTate (MonoidHom.id G) (𝟙 S.X₁)) (n + 1)
        ((zeroSplice_shortExact hS).δ n (n + 1) rfl x) =
      TateCohomology.δ hS n
        (HomologicalComplex.homologyMap (cochainsToTate (MonoidHom.id G) (𝟙 S.X₃)) n x) :=
  ConcreteCategory.congr_hom
    (cochainsToTate_delta hS hS (MonoidHom.id G) (𝟙 S) n) x

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype (G ⧸ H)] in
lemma cochainsToTate_subgroup_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) (x : (zeroSpliceComplex S.X₃).homology n) :
    HomologicalComplex.homologyMap (cochainsToTate H.subtype (𝟙 (Rep.res H.subtype S.X₁)))
        (n + 1) ((zeroSplice_shortExact hS).δ n (n + 1) rfl x) =
      TateCohomology.δ (hS.map_of_exact (Rep.resFunctor H.subtype)) n
        (HomologicalComplex.homologyMap
          (cochainsToTate H.subtype (𝟙 (Rep.res H.subtype S.X₃))) n x) :=
  ConcreteCategory.congr_hom
    (cochainsToTate_delta hS (hS.map_of_exact (Rep.resFunctor H.subtype))
      H.subtype (𝟙 (S.map (Rep.resFunctor H.subtype))) n) x

/-- Constructed Tate restriction agrees with the actual cochain comparison in nonnegative degrees. -/
lemma restriction_cochainsToTate (A : Rep.{u} R G) (n : ℕ)
    (x : (zeroSpliceComplex A).homology n) :
    restriction H A n
        (HomologicalComplex.homologyMap (cochainsToTate (MonoidHom.id G) (𝟙 A)) n x) =
      HomologicalComplex.homologyMap
        (cochainsToTate H.subtype (𝟙 (Rep.res H.subtype A))) n x := by
  induction n generalizing A with
  | zero =>
    obtain ⟨a, rfl⟩ := (zeroSpliceZeroEquiv A).symm.toLinearEquiv.surjective x
    exact (congrArg (restriction H A 0)
      (cochainsToTate_zero (MonoidHom.id G) (𝟙 A) a)).trans
        ((restrictionZero_zeroClass H a).trans
          (cochainsToTate_zero H.subtype (𝟙 (Rep.res H.subtype A)) a).symm)
  | succ n ih =>
    obtain ⟨y, rfl⟩ := zeroSplice_shiftUp_delta_surjective A n x
    refine (congrArg (restriction H A (n + 1))
      (cochainsToTate_identity_delta (shiftUpSequence A)
        (shiftUpSequence_shortExact A) n y)).trans ?_
    refine (restriction_scalarSplit_delta H (shiftUpSequence A)
      (shiftUpSequence_scalarSplitting A) n
      (HomologicalComplex.homologyMap
        (cochainsToTate (MonoidHom.id G) (𝟙 (shiftUp A))) n y)).trans ?_
    exact (congrArg
      (TateCohomology.δ ((shiftUpSequence_shortExact A).map_of_exact
        (Rep.resFunctor H.subtype)) n) (ih (shiftUp A) y)).trans
      (cochainsToTate_subgroup_delta H (shiftUpSequence A)
        (shiftUpSequence_shortExact A) n y).symm

/-- In every positive degree, constructed restriction is Mathlib's ordinary cohomology restriction. -/
theorem restriction_groupCohomology (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    ModuleCat.ofHom (restriction H A n) =
      ((TateCohomology.isoGroupCohomology n).app A).hom ≫
        groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n ≫
          ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)).inv := by
  have hh :
      HomologicalComplex.homologyMap (cochainsToTate (MonoidHom.id G) (𝟙 A)) n ≫
          ModuleCat.ofHom (restriction H A n) =
        HomologicalComplex.homologyMap
          (cochainsToTate H.subtype (𝟙 (Rep.res H.subtype A))) n := by
    ext x
    exact restriction_cochainsToTate H A n x
  rw [cochainsToTate_homology_id, cochainsToTate_homology] at hh
  apply (cancel_epi ((TateCohomology.isoGroupCohomology n).app A).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  exact (cancel_epi ((zeroSpliceConnectData A).homologyIsoPos n n rfl).hom).mp
    (by simpa only [Category.assoc] using hh)

end Langlands.Tate
