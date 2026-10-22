import Langlands.Cohomology.Tate.NegativeCorestriction

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Below the splice, the auxiliary homology of a coinduced replacement vanishes. -/
lemma zeroSplice_coinduced_neg_isZero (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    IsZero ((zeroSpliceComplex (coinduced A)).homology (-(n + 1 : ℤ))) :=
  (coinduced_tate_isZero A (-(n + 1 : ℤ))).of_iso
    ((zeroSpliceConnectData (coinduced A)).homologyIsoNeg n (-(n + 1 : ℤ)) rfl ≪≫
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app (coinduced A)).symm)

lemma tateToChains_identity_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) (x : tateCohomology S.X₃ n) :
    HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 S.X₁)) (n + 1)
        (TateCohomology.δ hS n x) =
      (zeroSplice_shortExact hS).δ n (n + 1) rfl
        (HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 S.X₃)) n x) :=
  ConcreteCategory.congr_hom
    (tateToChains_delta hS hS (MonoidHom.id G) (𝟙 S) n) x

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype (G ⧸ H)] in
lemma tateToChains_subgroup_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) (x : tateCohomology (Rep.res H.subtype S.X₃) n) :
    HomologicalComplex.homologyMap (tateToChains H.subtype (𝟙 (Rep.res H.subtype S.X₁)))
        (n + 1) (TateCohomology.δ (hS.map_of_exact (Rep.resFunctor H.subtype)) n x) =
      (zeroSplice_shortExact hS).δ n (n + 1) rfl
        (HomologicalComplex.homologyMap (tateToChains H.subtype
          (𝟙 (Rep.res H.subtype S.X₃))) n x) :=
  ConcreteCategory.congr_hom
    (tateToChains_delta (hS.map_of_exact (Rep.resFunctor H.subtype)) hS
      H.subtype (𝟙 (S.map (Rep.resFunctor H.subtype))) n) x

/-- The comparison equality propagates down one degree by an actual injective connecting map. -/
lemma corestriction_tateToChains_step (n : ℤ)
    (hz : ∀ A : Rep.{u} R G, IsZero ((zeroSpliceComplex (coinduced A)).homology n))
    (ih : ∀ (A : Rep.{u} R G) (x : tateCohomology (Rep.res H.subtype A) (n + 1)),
      HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 A)) (n + 1)
          (corestriction H A (n + 1) x) =
        HomologicalComplex.homologyMap (tateToChains H.subtype (𝟙 (Rep.res H.subtype A)))
          (n + 1) x)
    (A : Rep.{u} R G) (x : tateCohomology (Rep.res H.subtype A) n) :
    HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 A)) n
        (corestriction H A n x) =
      HomologicalComplex.homologyMap (tateToChains H.subtype (𝟙 (Rep.res H.subtype A))) n x := by
  have hm := (zeroSplice_shortExact (shiftDownSequence_shortExact A)).mono_δ
    n (n + 1) rfl (hz A)
  apply (ModuleCat.mono_iff_injective
    ((zeroSplice_shortExact (shiftDownSequence_shortExact A)).δ n (n + 1) rfl)).mp hm
  refine (tateToChains_identity_delta (shiftDownSequence A)
    (shiftDownSequence_shortExact A) n (corestriction H A n x)).symm.trans ?_
  refine (congrArg
    (HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 (shiftDown A))) (n + 1))
    (corestriction_scalarSplit_delta H (shiftDownSequence A)
      (shiftDownSequence_scalarSplitting A) n x).symm).trans ?_
  exact (ih (shiftDown A) _).trans
    (tateToChains_subgroup_delta H (shiftDownSequence A) (shiftDownSequence_shortExact A) n x)

/-- Constructed corestriction agrees with the ordinary chain comparison in every negative degree. -/
lemma corestriction_tateToChains (A : Rep.{u} R G) (n : ℕ)
    (x : tateCohomology (Rep.res H.subtype A) (-(n + 1 : ℤ))) :
    HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 A)) (-(n + 1 : ℤ))
        (corestriction H A (-(n + 1 : ℤ)) x) =
      HomologicalComplex.homologyMap (tateToChains H.subtype (𝟙 (Rep.res H.subtype A)))
        (-(n + 1 : ℤ)) x := by
  induction n generalizing A with
  | zero =>
    obtain ⟨a, ha, rfl⟩ := minusOneClass_surjective (Rep.res H.subtype A) x
    exact (congrArg
      (HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 A)) (-1))
      (corestriction_minusOneClass H A a ha)).trans
      ((tateToChains_minusOne (MonoidHom.id G) (𝟙 A) a
        (normZero_of_subgroup_normZero H A a ha)).trans
        (tateToChains_minusOne H.subtype (𝟙 (Rep.res H.subtype A)) a ha).symm)
  | succ n ih =>
    apply corestriction_tateToChains_step H (-(n + 1 + 1 : ℤ))
      (fun B => zeroSplice_coinduced_neg_isZero B (n + 1)) _ A x
    have he : -(n + 1 + 1 : ℤ) + 1 = -(n + 1 : ℤ) := by omega
    rw [he]
    exact ih

/-- In degrees at most minus two, Tate corestriction is Mathlib's ordinary homology pushforward. -/
theorem corestriction_groupHomology (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    ModuleCat.ofHom (corestriction H A (-(n + 1 : ℤ))) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app
        (Rep.res H.subtype A)).hom ≫
        groupHomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n ≫
          ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).inv := by
  have hh :
      ModuleCat.ofHom (corestriction H A (-(n + 1 : ℤ))) ≫
          HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 A)) (-(n + 1 : ℤ)) =
        HomologicalComplex.homologyMap (tateToChains H.subtype (𝟙 (Rep.res H.subtype A)))
          (-(n + 1 : ℤ)) := by
    ext x
    exact corestriction_tateToChains H A n x
  rw [tateToChains_homology_id, tateToChains_homology] at hh
  apply (cancel_mono ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono ((zeroSpliceConnectData A).homologyIsoNeg n (-(n + 1 : ℤ)) rfl).inv).mp
  simpa only [Category.assoc] using hh

end Langlands.Tate
