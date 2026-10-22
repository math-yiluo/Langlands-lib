import Langlands.Cohomology.Tate.HomologyTransferNaturality
import Langlands.Cohomology.Tate.NegativeHomologyComparison

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype (G ⧸ H)] in
/-- Restricted coinduced coefficients have no auxiliary homology below the splice. -/
lemma zeroSplice_restrictedCoinduced_neg_isZero (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    IsZero ((zeroSpliceComplex (Rep.res H.subtype (coinduced A))).homology
      (-(n + 1 : ℤ))) :=
  (restrictedCoinduced_tate_isZero H A (-(n + 1 : ℤ))).of_iso
    ((zeroSpliceConnectData (Rep.res H.subtype (coinduced A))).homologyIsoNeg
      n (-(n + 1 : ℤ)) rfl ≪≫
        ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app
          (Rep.res H.subtype (coinduced A))).symm)

/-- Injectivity of the auxiliary connecting map propagates the comparison downward. -/
lemma restriction_tateToTransferChains_step (n : ℤ)
    (hz : ∀ A : Rep.{u} R G,
      IsZero ((zeroSpliceComplex (Rep.res H.subtype (coinduced A))).homology n))
    (ih : ∀ (A : Rep.{u} R G) (x : tateCohomology A (n + 1)),
      HomologicalComplex.homologyMap
          (tateToChains (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) (n + 1)
          (restriction H A (n + 1) x) =
        HomologicalComplex.homologyMap (tateToTransferChains H A) (n + 1) x)
    (A : Rep.{u} R G) (x : tateCohomology A n) :
    HomologicalComplex.homologyMap
        (tateToChains (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) n
        (restriction H A n x) =
      HomologicalComplex.homologyMap (tateToTransferChains H A) n x := by
  have hS := (shiftDownSequence_shortExact A).map_of_exact (Rep.resFunctor H.subtype)
  have hm := (zeroSplice_shortExact hS).mono_δ n (n + 1) rfl (hz A)
  apply (ModuleCat.mono_iff_injective
    ((zeroSplice_shortExact hS).δ n (n + 1) rfl)).mp hm
  refine (tateToChains_identity_delta ((shiftDownSequence A).map (Rep.resFunctor H.subtype))
    hS n (restriction H A n x)).symm.trans ?_
  rw [← restriction_scalarSplit_delta H (shiftDownSequence A)
    (shiftDownSequence_scalarSplitting A) n x]
  exact (ih (shiftDown A) _).trans
    (ConcreteCategory.congr_hom
      (tateToTransferChains_delta H (shiftDownSequence A) (shiftDownSequence_shortExact A) n) x)

/-- Constructed Tate restriction agrees with the independent ordinary transfer comparison. -/
lemma restriction_tateToTransferChains (A : Rep.{u} R G) (n : ℕ)
    (x : tateCohomology A (-(n + 1 : ℤ))) :
    HomologicalComplex.homologyMap
        (tateToChains (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) (-(n + 1 : ℤ))
        (restriction H A (-(n + 1 : ℤ)) x) =
      HomologicalComplex.homologyMap (tateToTransferChains H A) (-(n + 1 : ℤ)) x := by
  induction n generalizing A with
  | zero =>
    obtain ⟨a, ha, rfl⟩ := minusOneClass_surjective A x
    change HomologicalComplex.homologyMap
        (tateToChains (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) (-1)
        (restriction H A (-1) (minusOneClass A a ha)) =
      HomologicalComplex.homologyMap (tateToTransferChains H A) (-1) (minusOneClass A a ha)
    erw [restriction_minusOneClass, tateToChains_minusOne, tateToTransferChains_minusOne]
    rfl
  | succ n ih =>
    apply restriction_tateToTransferChains_step H (-(n + 1 + 1 : ℤ))
      (fun B => zeroSplice_restrictedCoinduced_neg_isZero H B (n + 1)) _ A x
    have he : -(n + 1 + 1 : ℤ) + 1 = -(n + 1 : ℤ) := by omega
    rw [he]
    exact ih

/-- In degrees at most minus two, actual Tate restriction is ordinary homological transfer. -/
theorem restriction_groupHomology (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    ModuleCat.ofHom (restriction H A (-(n + 1 : ℤ))) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫
        ordinaryHomologyTransfer H A n ≫
          ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app
            (Rep.res H.subtype A)).inv := by
  have hh :
      ModuleCat.ofHom (restriction H A (-(n + 1 : ℤ))) ≫
          HomologicalComplex.homologyMap
            (tateToChains (MonoidHom.id H) (𝟙 (Rep.res H.subtype A))) (-(n + 1 : ℤ)) =
        HomologicalComplex.homologyMap (tateToTransferChains H A) (-(n + 1 : ℤ)) := by
    ext x
    exact restriction_tateToTransferChains H A n x
  rw [tateToChains_homology_id, tateToTransferChains_homology] at hh
  apply (cancel_mono ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app
    (Rep.res H.subtype A)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono
    ((zeroSpliceConnectData (Rep.res H.subtype A)).homologyIsoNeg
      n (-(n + 1 : ℤ)) rfl).inv).mp
  simpa only [Category.assoc] using hh

end Langlands.Tate
