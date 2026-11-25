/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAssembly
public import WeilConjectures.AlgebraicGeometry.Curve.GenericModelField
public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadSmooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange

/-!
# Spreading out the generic curve model

Let `B` be a noetherian domain with fraction field `L` and `f : X ⟶ Spec B` proper. A generic
curve model datum for the generic fibre `X_L` (`AlgebraicGeometry.IsGenericCurveModelData`)
spreads out to a generic curve model (`AlgebraicGeometry.IsGenericCurveModel`) of `X` over a
nonempty affine open of `Spec B` (`AlgebraicGeometry.exists_isGenericCurveModel_of_isFractionRing`).

We write `Spec L` as the cofiltered limit of the `Spec B[1/b]`. The finite morphisms of the datum
descend to finite morphisms at a stage (as in
`proposition-proper-direct-image-finite-coefficients`); smoothness and the closed immersion property
spread to later stages (EGA IV 8, 17), which are opens of the base; surjectivity and the finiteness
of the comparison boundary hold over the complement of a proper closed image
(`lem-weil-pbc-proper-closed-image`, `proposition-proper-direct-image-finite-coefficients`). This is
the spreading step of `proposition-proper-direct-image-finite-coefficients`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The map `Spec K ⟶ Spec R` induced by an injective ring map from a domain to a field hits
the generic point. -/
lemma SpecMap_apply_eq_genericPoint {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) (x : Spec (.of K)) :
    Spec.map (CommRingCat.ofHom φ) x = genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap φ x.asIdeal = _
  rw [Ideal.eq_bot_of_prime x.asIdeal, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
  rfl

/-- The base change along `j : S' ⟶ S` of a morphism `γ` in `Over S` is a base change of
`γ.left`. -/
lemma isPullback_over_pullback_map {S S' : Scheme.{u}} (j : S' ⟶ S) {Z Y : Over S}
    (γ : Z ⟶ Y) :
    IsPullback (pullback.fst Z.hom j) ((Over.pullback j).map γ).left γ.left
      (pullback.fst Y.hom j) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback Y.hom j)
  simpa [Over.w γ] using IsPullback.of_hasPullback Z.hom j

/-- Two cartesian squares over `γ` with compatible bottom maps: a property stable under base
change passes from the first base change of `γ` to the second. -/
lemma MorphismProperty.of_isPullback_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z Y Z₁ Y₁ Z₂ Y₂ : Scheme.{u}} {γ : Z ⟶ Y} {γ₁ : Z₁ ⟶ Y₁}
    {γ₂ : Z₂ ⟶ Y₂} {a₁ : Z₁ ⟶ Z} {b₁ : Y₁ ⟶ Y} {a₂ : Z₂ ⟶ Z} {b₂ : Y₂ ⟶ Y}
    (H₁ : IsPullback a₁ γ₁ γ b₁) (H₂ : IsPullback a₂ γ₂ γ b₂) (e : Y₂ ⟶ Y₁)
    (he : e ≫ b₁ = b₂) (h : P γ₁) : P γ₂ := by
  let l : Z₂ ⟶ Z₁ := H₁.lift a₂ (γ₂ ≫ e) (by rw [Category.assoc, he, H₂.w])
  have H : IsPullback l γ₂ γ₁ e := by
    refine IsPullback.of_right ?_ (H₁.lift_snd _ _ _) H₁
    rw [H₁.lift_fst, he]
    exact H₂
  exact P.of_isPullback H h

/-- A base change along an open immersion `j` has a property `P` if and only if the restriction
over the image of `j` has it. -/
lemma iff_morphismRestrict_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Z Y Z' V : Scheme.{u}} {γ : Z ⟶ Y} {γ' : Z' ⟶ V} {a : Z' ⟶ Z} {j : V ⟶ Y}
    [IsOpenImmersion j] (H : IsPullback a γ' γ j) : P γ' ↔ P (γ ∣_ j.opensRange) := by
  rw [← H.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).trans
    (pullback_snd_iff_morphismRestrict P γ j)

/-- Two factorizations of the same morphism agree pointwise. -/
lemma Scheme.Hom.apply_eq_of_comp_eq {A B C D : Scheme.{u}} {f₁ : A ⟶ B} {g₁ : B ⟶ C}
    {f₂ : A ⟶ D} {g₂ : D ⟶ C} (h : f₁ ≫ g₁ = f₂ ≫ g₂) (a : A) : g₁ (f₁ a) = g₂ (f₂ a) := by
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]

/-- **Spreading out the generic curve model.** Let `B` be a noetherian domain with fraction
field `L` and `f : X ⟶ Spec B` proper. If the generic fibre `X_L` has a generic curve model
datum, then over some nonempty affine integral open `S' ⊆ Spec B` (given by the open immersion
`ρ`), the restriction `X' ⟶ S'` of `f` has a generic curve model. -/
theorem exists_isGenericCurveModel_of_isFractionRing {B L : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f]
    (hX : IsGenericCurveModelData
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B L))))) :
    ∃ (S' : Scheme.{u}) (_ : IsAffine S') (_ : IsIntegral S') (ρ : S' ⟶ Spec (.of B))
      (_ : IsOpenImmersion ρ) (X' : Scheme.{u}) (F' : X' ⟶ S') (iX : X' ⟶ X),
      IsPullback iX F' f ρ ∧ IsGenericCurveModel F' := by
  classical
  obtain ⟨ι, _, Y₀, ν, d, W, hfin, hsm, hsurj, hci, hWfin⟩ := hX
  have := Fintype.ofFinite ι
  obtain ⟨pt⟩ : Nonempty (Spec (.of L)) := inferInstance
  -- `Spec L` as the limit of the `Spec B[1/b]`
  have : IsLocalization (⊥ : Ideal B).primeCompl L := by
    rw [Ideal.primeCompl_bot]; infer_instance
  let eK : CommRingCat.of (Localization.AtPrime (⊥ : Ideal B)) ≅ CommRingCat.of L :=
    (IsLocalization.algEquiv (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B))
      L).toRingEquiv.toCommRingCatIso
  let cR := (CommRingCat.awayProdCocone (⊥ : Ideal B)).extend eK.hom
  have hR : IsColimit cR := (CommRingCat.isColimitAwayProdCocone _).ofIsoColimit
    (Cocone.ext eK fun _ ↦ rfl)
  have hRA (s : Finset (⊥ : Ideal B).primeCompl) :
      CommRingCat.ofHom (algebraMap B (CommRingCat.AwayProd ⊥ s)) ≫ cR.ι.app s =
        CommRingCat.ofHom (algebraMap B L) := by
    change _ ≫ _ ≫ eK.hom = _
    rw [CommRingCat.ofHom_algebraMap_comp_awayProdCocone_ι_app_assoc]
    ext x
    exact (IsLocalization.algEquiv (⊥ : Ideal B).primeCompl
      (Localization.AtPrime (⊥ : Ideal B)) L).commutes x
  let I := (Finset (⊥ : Ideal B).primeCompl)ᵒᵖ
  let D₀ : I ⥤ Scheme.{u} := (CommRingCat.awayProdDiagram (⊥ : Ideal B)).op ⋙ Scheme.Spec
  let c₀ : Cone D₀ := Scheme.Spec.mapCone cR.op
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec hR.op
  let q (s : I) : D₀.obj s ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B (CommRingCat.AwayProd ⊥ s.unop)))
  have hq {s s' : I} (u : s ⟶ s') : D₀.map u ≫ q s' = q s := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.ofHom_algebraMap_comp_awayProdDiagram_map _ u.unop)
  let q₀ : Spec (.of L) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B L))
  have hq₀ (s : I) : c₀.π.app s ≫ q s = q₀ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (hRA s.unop)
  have : IsConnected I := IsCofiltered.isConnected I
  have : ∀ {s s' : I} (u : s ⟶ s'), IsAffineHom (D₀.map u) := fun u ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have (s : I) : IsAffine (D₀.obj s) := inferInstanceAs (IsAffine (Spec _))
  have hqo (s : I) : IsOpenImmersion (q s) :=
    IsOpenImmersion.of_isLocalization (∏ x ∈ s.unop, (x : B))
  have hD₀o {s s' : I} (u : s ⟶ s') : IsOpenImmersion (D₀.map u) := by
    have := hqo s'
    have : IsOpenImmersion (D₀.map u ≫ q s') := by
      rw [hq u]
      exact hqo s
    exact IsOpenImmersion.of_comp _ (q s')
  have hdom (s : I) : IsDomain (CommRingCat.AwayProd (⊥ : Ideal B) s.unop) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Finset.prod_ne_zero_iff.mpr fun x _ hx ↦ x.2 (by simp [hx])))
  have hint (s : I) : IsIntegral (D₀.obj s) := by
    have := hdom s
    exact inferInstanceAs (IsIntegral (Spec (.of (CommRingCat.AwayProd (⊥ : Ideal B) s.unop))))
  have hnoeth (s : I) : IsNoetherian (D₀.obj s) := by
    exact inferInstanceAs (IsNoetherian (Spec (.of (CommRingCat.AwayProd (⊥ : Ideal B) s.unop))))
  have hgen (s : I) (x : Spec (.of L)) : c₀.π.app s x = genericPoint (D₀.obj s) := by
    have := hdom s
    have := hint s
    have hφ : (cR.ι.app s.unop).hom.comp (algebraMap B (CommRingCat.AwayProd ⊥ s.unop)) =
        algebraMap B L :=
      congrArg CommRingCat.Hom.hom (hRA s.unop)
    exact SpecMap_apply_eq_genericPoint (K := L) (R := CommRingCat.AwayProd ⊥ s.unop)
      (cR.ι.app s.unop).hom (injective_awayProd_fractionRing s.unop _ hφ) x
  -- the base changed system with limit `X_L`
  let D := baseChangeOverFamilyDiagram D₀ q hq f
  let c := baseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f
  have hc : IsLimit c := isLimitBaseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f hc₀
  have (s : I) : CompactSpace (D.obj s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (q s))
  have (s : I) : QuasiSeparatedSpace (D.obj s) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (q s))
  have : IsLocallyNoetherian (pullback f q₀) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f q₀)
  have : CompactSpace ↥(pullback f q₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f q₀)
  have : IsNoetherian (pullback f q₀) := {}
  have : TopologicalSpace.NoetherianSpace c.pt :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(pullback f q₀))
  have HX (s : I) : IsPullback (c.π.app s) (pullback.snd f q₀) (pullback.snd f (q s))
      (c₀.π.app s) :=
    isPullback_pullback_map f q₀ (q s) (c₀.π.app s) (hq₀ s)
  -- descend the finite morphisms and the open `W` to a stage `s₀`
  obtain ⟨jW, OW, -, hOW⟩ := exists_preimage_eq D c hc W
    (TopologicalSpace.NoetherianSpace.isCompact _)
  let Good (a : ι) (s : I) : Prop := ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj s) (h : Y₀ a ⟶ Y),
    IsFinite p ∧ IsPullback h (ν a) p (c.π.app s)
  have hmono (a : ι) {s s' : I} (u : s' ⟶ s) (h : Good a s) : Good a s' := by
    obtain ⟨Y, p, h, hp, H⟩ := h
    exact ⟨_, pullback.snd p (D.map u), isPullbackLift D c u H, inferInstance,
      isPullback_isPullbackLift u H⟩
  have hex (a : ι) : ∃ s, Good a s := by
    have := (IsFinite.locallyOfFinitePresentation_of_isLocallyNoetherian (ν a)).1
    obtain ⟨s, Y, p, _, _, _, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc (ν a)
    have : IsFinite (pullback.snd p (c.π.app s)) := by
      rw [← H.isoPullback_inv_snd]
      infer_instance
    obtain ⟨s', u, hu⟩ := Scheme.exists_isFinite_pullback_snd_of_isLimit hc p
    exact ⟨s', _, pullback.snd p (D.map u), isPullbackLift D c u H, hu,
      isPullback_isPullbackLift u H⟩
  choose s₁ hs₁ using hex
  obtain ⟨s₀, hs⟩ := IsCofiltered.inf_objs_exists (insert jW (Finset.univ.image s₁))
  have hgood (a : ι) : Good a s₀ :=
    hmono a (hs (Finset.mem_insert_of_mem (Finset.mem_image_of_mem s₁
      (Finset.mem_univ a)))).some (hs₁ a)
  choose Y p h hp H using hgood
  let uW : s₀ ⟶ jW := (hs (Finset.mem_insert_self _ _)).some
  let W₀ : (D.obj s₀).Opens := D.map uW ⁻¹ᵁ OW
  have hW₀ : c.π.app s₀ ⁻¹ᵁ W₀ = W := by
    rw [← Scheme.Hom.comp_preimage, c.w uW, hOW]
  -- the base `S₀ = Spec B[1/b]` and the morphism `F₀ : X₀ ⟶ S₀`
  let S₀ := D₀.obj s₀
  have : IsIntegral S₀ := hint s₀
  have : IsNoetherian S₀ := hnoeth s₀
  let F₀ : D.obj s₀ ⟶ S₀ := pullback.snd f (q s₀)
  have : IsNoetherian (D.obj s₀) := isNoetherian_of_locallyOfFiniteType F₀
  let j := c₀.π.app s₀
  have H' (a : ι) : IsPullback (h a) (ν a ≫ pullback.snd f q₀) (p a ≫ F₀) j :=
    (H a).paste_vert (HX s₀)
  have hηmem {s : I} (w : s ⟶ s₀) : genericPoint S₀ ∈ (D₀.map w).opensRange :=
    ⟨c₀.π.app s pt, by rw [← Scheme.Hom.comp_apply, c₀.w w]; exact hgen s₀ pt⟩
  -- smoothness spreads
  have hsm₁ (a : ι) : ∃ (s : I) (u : s ⟶ s₀), Smooth (pullback.snd (p a ≫ F₀) (D₀.map u)) := by
    have : Smooth (pullback.snd (p a ≫ F₀) j) := by
      have := (hsm a).2
      have : Smooth (ν a ≫ pullback.snd f q₀) := SmoothOfRelativeDimension.smooth (d a) _
      rw [← (H' a).isoPullback_inv_snd]
      infer_instance
    exact Scheme.exists_smooth_pullback_snd_of_isLimit hc₀ (p a ≫ F₀)
  choose s₂ u₂ hu₂ using hsm₁
  obtain ⟨s₃, hs₃⟩ := IsCofiltered.inf_objs_exists (insert s₀ (Finset.univ.image s₂))
  let w₃ : s₃ ⟶ s₀ := (hs₃ (Finset.mem_insert_self _ _)).some
  have hsmV (a : ι) : Smooth ((p a ≫ F₀) ∣_ (D₀.map w₃).opensRange) := by
    let v : s₃ ⟶ s₂ a := (hs₃ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem s₂
      (Finset.mem_univ a)))).some
    have := hD₀o (u₂ a)
    have h1 := (pullback_snd_iff_morphismRestrict @Smooth (p a ≫ F₀) (D₀.map (u₂ a))).mp (hu₂ a)
    refine Scheme.Hom.restrict_of_le _ _ ?_ h1
    rintro _ ⟨x, rfl⟩
    refine ⟨D₀.map v x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    congr 2
  -- the closed immersion property over `W₀` spreads
  let ν₀ := Sigma.desc p
  have Hσ : IsPullback (Limits.Sigma.map h) (Sigma.desc ν) ν₀ (c.π.app s₀) :=
    isPullback_sigmaDesc p ν h (c.π.app s₀) H
  let Yo : Over S₀ := Over.mk (W₀.ι ≫ F₀)
  let Zo : Over S₀ := Over.mk (ν₀ ∣_ W₀ ≫ W₀.ι ≫ F₀)
  let γo : Zo ⟶ Yo := Over.homMk (ν₀ ∣_ W₀) rfl
  have hS : IsClosedImmersion ((Over.pullback j).map γo).left := by
    obtain ⟨a', -, Ha'⟩ := AlgebraicGeometry.IsPullback.exists_isPullback_morphismRestrict Hσ W₀
    have h1 : IsClosedImmersion (Sigma.desc ν ∣_ (c.π.app s₀ ⁻¹ᵁ W₀)) :=
      Scheme.Hom.restrict_of_le _ _ hW₀.le hci
    have HW : IsPullback (c.π.app s₀ ∣_ W₀) ((c.π.app s₀ ⁻¹ᵁ W₀).ι ≫ pullback.snd f q₀)
        (W₀.ι ≫ F₀) j :=
      (isPullback_morphismRestrict (c.π.app s₀) W₀).paste_vert (HX s₀)
    exact MorphismProperty.of_isPullback_of_isPullback @IsClosedImmersion Ha'
      (isPullback_over_pullback_map j γo)
      (HW.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition) (HW.lift_fst _ _ _) h1
  have : LocallyOfFinitePresentation γo.left :=
    (IsFinite.locallyOfFinitePresentation_of_isLocallyNoetherian (ν₀ ∣_ W₀)).1
  have : QuasiCompact γo.left := inferInstanceAs (QuasiCompact (ν₀ ∣_ W₀))
  have : QuasiSeparated γo.left := inferInstanceAs (QuasiSeparated (ν₀ ∣_ W₀))
  have : CompactSpace Yo.left :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W₀ : Set (D.obj s₀)))
  have : QuasiSeparatedSpace Yo.left := inferInstanceAs (QuasiSeparatedSpace W₀.toScheme)
  obtain ⟨s₄, u₄, hu₄⟩ := Scheme.exists_isClosedImmersion_overPullbackMap hc₀ γo hS
  have h4 := hu₄ (𝟙 s₄)
  rw [Category.id_comp] at h4
  have := hD₀o u₄
  have h4' : IsClosedImmersion
      ((ν₀ ∣_ W₀) ∣_ (pullback.fst Yo.hom (D₀.map u₄)).opensRange) :=
    (iff_morphismRestrict_of_isPullback @IsClosedImmersion
      (isPullback_over_pullback_map _ γo)).mp h4
  have hci₀ : IsClosedImmersion (ν₀ ∣_ (W₀ ⊓ F₀ ⁻¹ᵁ (D₀.map u₄).opensRange)) := by
    have h5 := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (morphismRestrictRestrict ν₀ W₀ (pullback.fst Yo.hom (D₀.map u₄)).opensRange)).mp h4'
    refine Scheme.Hom.restrict_of_le _ _ ?_ h5
    rintro x ⟨hxW, hxV⟩
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact hxV
  -- surjectivity over an open neighbourhood of the generic point
  have hlift (z : D.obj s₀) (hz : F₀ z = genericPoint S₀) :
      ∃ z' : c.pt, c.π.app s₀ z' = z := by
    obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := F₀) (g := j) z pt
      (by rw [hz, hgen])
    refine ⟨(HX s₀).isoPullback.inv w, ?_⟩
    rw [← hw₁, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  have hO : IsOpen (Set.range ν₀)ᶜ := ν₀.isClosedMap.isClosed_range.isOpen_compl
  obtain ⟨Vs, hηs, hVs⟩ := exists_genericPoint_mem_forall_notMem F₀ hO (by
    intro z hz hzη
    apply hz
    obtain ⟨z', rfl⟩ := hlift z hzη
    obtain ⟨y, rfl⟩ := hsurj.surj z'
    exact ⟨Limits.Sigma.map h y, Scheme.Hom.apply_eq_of_comp_eq Hσ.w y⟩)
  -- the complement of `W₀` is finite over an open neighbourhood of the generic point
  let C : TopologicalSpace.Closeds (D.obj s₀) := ⟨(W₀ : Set (D.obj s₀))ᶜ, W₀.isOpen.isClosed_compl⟩
  let d₀ := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hd₀ : Set.range d₀ = (W₀ : Set (D.obj s₀))ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hfib : ((d₀ ≫ F₀) ⁻¹' {genericPoint S₀}).Finite := by
    refine ((hWfin.image (c.π.app s₀)).preimage d₀.isClosedEmbedding.injective.injOn).subset ?_
    intro y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply] at hy
    obtain ⟨z', hz'⟩ := hlift (d₀ y) hy
    refine ⟨z', fun hz'W ↦ ?_, hz'⟩
    have hy' : d₀ y ∈ Set.range d₀ := ⟨y, rfl⟩
    rw [hd₀] at hy'
    apply hy'
    rw [← hz']
    rw [← hW₀] at hz'W
    exact hz'W
  obtain ⟨VD, hηD, hVD⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton (d₀ ≫ F₀) _ hfib
  -- an affine open neighbourhood of the generic point inside all these opens
  let V₁ : S₀.Opens := (D₀.map w₃).opensRange ⊓ (D₀.map u₄).opensRange ⊓ Vs ⊓ VD
  have hηV₁ : genericPoint S₀ ∈ V₁ := by
    simp only [V₁, TopologicalSpace.Opens.mem_inf]
    exact ⟨⟨⟨hηmem w₃, hηmem u₄⟩, hηs⟩, hηD⟩
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hηU, hUV⟩ :=
    S₀.isBasis_affineOpens.exists_subset_of_mem_open hηV₁ V₁.isOpen
  let U : S₀.Opens := U₀
  have hUle : U ≤ V₁ := hUV
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hciU : IsClosedImmersion (ν₀ ∣_ (W₀ ⊓ F₀ ⁻¹ᵁ U)) := by
    refine Scheme.Hom.restrict_of_le _ _ ?_ hci₀
    rintro x ⟨hxW, hxU⟩
    exact ⟨hxW, (hUle hxU).1.1.2⟩
  have hmodel := isGenericCurveModel_morphismRestrict F₀ p j (hgen s₀)
    (fun a ↦ ν a ≫ pullback.snd f q₀) h H' d (fun a ↦ (hsm a).1) (fun a ↦ (hsm a).2) W₀ U hηU
    (fun a ↦ Scheme.Hom.restrict_of_le _ _ (fun x hx ↦ (hUle hx).1.1.1) (hsmV a))
    hciU
    (fun x hx ↦ by
      by_contra hxν
      exact hVs x hxν (hUle hx).1.2)
    (fun s hs ↦ by
      have := hVD
      refine (((d₀ ≫ F₀).finite_preimage_singleton_of_isFinite_morphismRestrict
        (hUle hs).2).image d₀).subset ?_
      rintro x ⟨hxs, hxW⟩
      obtain ⟨y, rfl⟩ : x ∈ Set.range d₀ := by rw [hd₀]; exact hxW
      exact ⟨y, hxs, rfl⟩)
  refine ⟨U.toScheme, hU, isIntegral_of_isOpenImmersion U.ι, U.ι ≫ q s₀, inferInstance,
    (F₀ ⁻¹ᵁ U).toScheme, F₀ ∣_ U, (F₀ ⁻¹ᵁ U).ι ≫ pullback.fst f (q s₀), ?_, hmodel⟩
  exact (isPullback_morphismRestrict F₀ U).flip.paste_horiz (IsPullback.of_hasPullback f (q s₀))

end AlgebraicGeometry
