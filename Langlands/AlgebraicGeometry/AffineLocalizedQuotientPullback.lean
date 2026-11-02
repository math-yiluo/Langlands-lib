import Langlands.AlgebraicGeometry.AffineQuotientPullback
import Langlands.AlgebraicGeometry.SchemeEtaleLocus

/-! # Localized quotients inside affine pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The localized affine slice is an open subspace of the full affine pullback. -/
def affineLocalizedQuotientToPullback (θ : A →+* B) (I : Ideal A) (g : B) :
    Spec (CommRingCat.of ((Localization.Away g) ⧸
      I.map ((algebraMap B (Localization.Away g)).comp θ))) ⟶
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom θ)) :=
  (affineQuotientPullbackIso ((algebraMap B (Localization.Away g)).comp θ) I).hom ≫
    pullback.map _ _ _ _ (𝟙 _)
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))) (𝟙 _)
      (by simp) (by simp [CommRingCat.ofHom_comp, Spec.map_comp])

instance isOpenImmersion_affineLocalizedQuotientToPullback
    (θ : A →+* B) (I : Ideal A) (g : B) :
    IsOpenImmersion (affineLocalizedQuotientToPullback θ I g) := by
  unfold affineLocalizedQuotientToPullback
  infer_instance

@[reassoc (attr := simp)]
lemma affineLocalizedQuotientToPullback_snd (θ : A →+* B) (I : Ideal A) (g : B) :
    affineLocalizedQuotientToPullback θ I g ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map ((algebraMap B (Localization.Away g)).comp θ)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) := by
  unfold affineLocalizedQuotientToPullback
  rw [Category.assoc]
  simp only [pullback.map, pullback.lift_snd]
  rw [← Category.assoc, affineQuotientPullbackIso_hom_snd]


/-- A prime containing the pulled-back equations lifts to the localized quotient. -/
lemma exists_affineLocalizedQuotientPoint (θ : A →+* B) (I : Ideal A) (g : B)
    (q : Spec (CommRingCat.of B)) (hg : g ∉ q.asIdeal)
    (hI : I ≤ q.asIdeal.comap θ) :
    ∃ z : Spec (CommRingCat.of ((Localization.Away g) ⧸
      I.map ((algebraMap B (Localization.Away g)).comp θ))),
      (affineLocalizedQuotientToPullback θ I g ≫ pullback.snd _ _) z = q := by
  obtain ⟨q', hq'⟩ : q ∈ Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))) := by
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g)))
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have hqI : q'.asIdeal.comap (algebraMap B (Localization.Away g)) = q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hq'
  have hI' : I.map ((algebraMap B (Localization.Away g)).comp θ) ≤ q'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    change I ≤ (q'.asIdeal.comap (algebraMap B (Localization.Away g))).comap θ
    rw [hqI]
    exact hI
  obtain ⟨z, hz⟩ := (mem_range_SpecMap_quotient_iff _ q').mpr hI'
  refine ⟨z, ?_⟩
  rw [affineLocalizedQuotientToPullback_snd, Scheme.Hom.comp_apply, hz]
  exact hq'

/-- Etaleness on an open neighborhood implies formal etaleness of the ambient stalk. -/
lemma formallyEtale_stalk_of_etale_open {V X Y : Scheme.{u}}
    (i : V ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [Etale (i ≫ f)] (z : V) :
    (f.stalkMap (i z)).hom.FormallyEtale := by
  have hz := (schemeEtaleLocus_eq_top (i ≫ f)).ge (Set.mem_univ z)
  change ((i ≫ f).stalkMap z).hom.FormallyEtale at hz
  apply (formallyEtale_respectsIso.cancel_right_isIso _ (i.stalkMap z)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact hz

/-- A localized etale quotient gives an etale open neighborhood in the pullback. -/
lemma etale_affineLocalizedQuotientToPullback_comp (σ θ : A →+* B) (I : Ideal A) (g : B)
    (he : (((Ideal.Quotient.mk (I.map ((algebraMap B (Localization.Away g)).comp θ))).comp
      (algebraMap B (Localization.Away g))).comp σ).Etale) :
    Etale (affineLocalizedQuotientToPullback θ I g ≫
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ))) := by
  rw [← Category.assoc, affineLocalizedQuotientToPullback_snd]
  simp only [← Spec.map_comp]
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he

/-- Lift an allowed prime to a formally etale stalk of the affine slice pullback. -/
lemma exists_formallyEtale_stalk_affinePullback (σ θ : A →+* B) (I : Ideal A) (g : B)
    (q : Spec (CommRingCat.of B)) (hg : g ∉ q.asIdeal)
    (hI : I ≤ q.asIdeal.comap θ)
    (he : (((Ideal.Quotient.mk (I.map ((algebraMap B (Localization.Away g)).comp θ))).comp
      (algebraMap B (Localization.Away g))).comp σ).Etale) :
    ∃ b : (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom θ)) : Scheme.{u}),
      (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom θ))) b = q ∧
      ((pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ)).stalkMap b).hom.FormallyEtale := by
  obtain ⟨z, hz⟩ := exists_affineLocalizedQuotientPoint θ I g q hg hI
  let := etale_affineLocalizedQuotientToPullback_comp σ θ I g he
  exact ⟨affineLocalizedQuotientToPullback θ I g z, hz,
    formallyEtale_stalk_of_etale_open _ _ z⟩

end Langlands.AlgebraicGeometry
