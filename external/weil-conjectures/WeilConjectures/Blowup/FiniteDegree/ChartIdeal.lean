/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.ChartProbe

/-!
# Chart ideals and membership along maps for the finite-degree approximation

The chart ideals of an ideal sheaf on the blow-up, and the transport of memberships along
morphisms of rings.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section ChartIdeal

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- The chart model of the ideal of sections of an ideal sheaf `J` on the blow-up over
the `a`-chart: the ideal of sections of the pullback of `J` along the chart probe,
transported to the chart ring along the global-sections isomorphism. -/
def Scheme.IdealSheafData.chartIdeal (I : X.IdealSheafData) (J : I.blowup.IdealSheafData)
    (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Ideal (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha)) :=
  ((J.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso _).hom.hom

/-- Membership in the chart model of `J` is membership of the transported section in
the ideal of sections of the pullback of `J`. -/
lemma Scheme.IdealSheafData.mem_chartIdeal_iff (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)}
    (ha : a ∈ I.ideal V)
    {z : HomogeneousLocalization.Away (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)} :
    z ∈ I.chartIdeal J V ha ↔ (Scheme.ΓSpecIso _).inv.hom z ∈
      (J.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  have hx : (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
      (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)))).inv.hom z) = z := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  conv_lhs => rw [← hx]
  exact CommRingCat.hom_mem_ideal_map_iso_iff _ _ _

/-- The chart model of a finite-type ideal sheaf is finitely generated. -/
lemma Scheme.IdealSheafData.chartIdeal_fg (I : X.IdealSheafData)
    {J : I.blowup.IdealSheafData} (hJ : J.ofFiniteType) (V : X.affineOpens)
    {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) : (I.chartIdeal J V ha).FG :=
  ((hJ.comap_of_isOpenImmersion (I.blowupChart V ha)) ⟨⊤, isAffineOpen_top _⟩ le_top).map _

/-- The chart models of `J` on two charts of the same Rees algebra agree in the common
localization `B_{b·a}`: transport of the pullback of `J` along the overlap probe. The
orientation matches the hypothesis of
`AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem`. -/
lemma Scheme.IdealSheafData.chartIdeal_map_awayMap (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) (V : X.affineOpens) {a b : Γ(X, V.1)}
    (ha : a ∈ I.ideal V) (hb : b ∈ I.ideal V) :
    (I.chartIdeal J V ha).map (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) b hb)
        (mul_comm (reesX (I.ideal V) b hb) (reesX (I.ideal V) a ha))) =
      (I.chartIdeal J V hb).map (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) a ha)
        (rfl : reesX (I.ideal V) b hb * reesX (I.ideal V) a ha
          = reesX (I.ideal V) b hb * reesX (I.ideal V) a ha)) := by
  have h1 := J.map_ideal_comap_specMap_comp (I.blowupChart V ha)
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
      (reesX_mem (I.ideal V) b hb)
      (mul_comm (reesX (I.ideal V) b hb) (reesX (I.ideal V) a ha))))
  have h2 := J.map_ideal_comap_specMap_comp (I.blowupChart V hb)
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
      (reesX_mem (I.ideal V) a ha)
      (rfl : reesX (I.ideal V) b hb * reesX (I.ideal V) a ha
        = reesX (I.ideal V) b hb * reesX (I.ideal V) a ha)))
  -- the two overlap probes agree
  have hmid := congrArg
    (fun q : Spec (CommRingCat.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) b hb * reesX (I.ideal V) a ha))) ⟶ I.blowup ↦
      ((J.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso _).hom.hom)
    (I.specMap_awayMap_blowupChart V hb ha)
  exact (h1.symm.trans (hmid.symm.trans h2) :)

end ChartIdeal

section MapMembership

variable {X Y : Scheme.{u}}

/-- **Membership in the pushforward ideal through a covering family of affine probes**:
let `g : Y ⟶ X` be quasi-compact, `K` an ideal sheaf on `Y`, `V` an affine open of `X`
and `x` a section over `V`. Suppose given open-immersion probes `cᵢ : Spec Sᵢ ⟶ Y`
lying over `V` and covering `g⁻¹(V)`, such that the pullback of `x` to each probe lies
in the ideal of sections of the pullback of `K`. Then `x` lies in the ideal of the
pushforward `K.map g` over `V`. This makes the blueprint's maximal candidate
`π₎(I_E^d J)` accessible chart by chart. -/
lemma Scheme.IdealSheafData.mem_ideal_map_of_probes (K : Y.IdealSheafData)
    (g : Y ⟶ X) [QuasiCompact g] (V : X.affineOpens) (x : Γ(X, V.1))
    {ι : Type u} {S : ι → CommRingCat.{u}} (c : ∀ i, Spec (S i) ⟶ Y)
    [∀ i, IsOpenImmersion (c i)]
    (hcov : (g ⁻¹ᵁ V.1 : Set Y) ⊆ ⋃ i, Set.range (c i))
    (hle : ∀ i, (⊤ : (Spec (S i)).Opens) ≤ (c i ≫ g) ⁻¹ᵁ V.1)
    (hx : ∀ i, ((c i ≫ g).appLE V.1 ⊤ (hle i)).hom x ∈
      (K.comap (c i)).ideal ⟨⊤, isAffineOpen_top _⟩) :
    x ∈ (K.map g).ideal V := by
  have : QuasiCompact (K.subschemeι ≫ g) := inferInstance
  change x ∈ (K.subschemeι ≫ g).ker.ideal V
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  apply K.subscheme.IsSheaf.section_ext
  intro p hp
  -- the image of `p` in `Y` lies over `V`, hence in the range of some probe
  have hpV : K.subschemeι p ∈ (g ⁻¹ᵁ V.1 : Set Y) := by
    change g (K.subschemeι p) ∈ V.1
    rw [← Scheme.Hom.comp_apply]
    exact hp
  obtain ⟨_, ⟨i, rfl⟩, y, hy⟩ := hcov hpV
  -- the pullback of the probe to the subscheme
  have : IsClosedImmersion (pullback.fst (c i) K.subschemeι) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hprange : p ∈ Set.range (pullback.snd (c i) K.subschemeι) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, hy⟩
  obtain ⟨q, hq⟩ := hprange
  -- the composite of the pullback square with the probe
  have hcomp : pullback.snd (c i) K.subschemeι ≫ K.subschemeι ≫ g =
      pullback.fst (c i) K.subschemeι ≫ (c i ≫ g) := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
  -- the witnessing open: the image of the preimage of `(subschemeι ≫ g)⁻¹(V)`
  refine ⟨pullback.snd (c i) K.subschemeι ''ᵁ
    (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1)), ?_,
    ⟨q, ?_, hq⟩, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hw
  · change pullback.snd (c i) K.subschemeι q ∈ (K.subschemeι ≫ g) ⁻¹ᵁ V.1
    rw [hq]
    exact hp
  -- both restrictions are computed by pulling back to the probe
  rw [map_zero]
  apply ((pullback.snd (c i) K.subschemeι).appIso
    (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1))
      ).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  -- exchange the composite for the probe composite and split off the probe map
  rw [Scheme.Hom.appLE_eq_of_eq hcomp]
  rw [← Scheme.Hom.appLE_comp_appLE (pullback.fst (c i) K.subschemeι) (c i ≫ g)
    V.1 ⊤ (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1))
    (hle i) le_top]
  rw [CommRingCat.comp_apply]
  -- the probe image of `x` is killed by the closed immersion from the subscheme part
  have h0 : ((pullback.fst (c i) K.subschemeι).app ⊤).hom
      (((c i ≫ g).appLE V.1 ⊤ (hle i)).hom x) = 0 := by
    apply Scheme.Hom.ideal_ker_le _ ⟨⊤, isAffineOpen_top _⟩
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_subschemeι]
    exact hx i
  have hexp : (pullback.fst (c i) K.subschemeι).appLE ⊤
      (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1)) le_top =
      (pullback.fst (c i) K.subschemeι).app ⊤ ≫
        (Limits.pullback (c i) K.subschemeι).presheaf.map (homOfLE le_top).op := rfl
  rw [hexp, CommRingCat.comp_apply, h0, map_zero]

end MapMembership

end AlgebraicGeometry
