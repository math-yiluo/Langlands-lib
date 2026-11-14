import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReductionStatement
import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-! # Proof of the reduction of relative effective divisors to the Hilbert scheme and the
relative effective Cartier locus -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReduction

open Langlands.AlgebraicGeometry.Modules

section Cartier

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual ideal of an effective Cartier divisor has finitely generated sections over every
affine open. -/
lemma hasFiniteAffineSections_kernelModule (hI : IsEffectiveCartierIdeal I) :
    HasFiniteAffineSections (StructureKernelModule.kernelModule I.subschemeι) := by
  have : (StructureKernelModule.kernelModule I.subschemeι).IsQuasicoherent :=
    StructureKernelModule.kernelModule_isQuasicoherent _
  refine HasLocallyFiniteSections.finiteAffineSections
    (HasLocallyFiniteSections.of_locally_finiteAffineSections fun x => ?_)
  obtain ⟨O, hxO, ⟨e⟩⟩ := hI x
  refine ⟨O, hxO, HasFiniteAffineSections.of_iso e.symm ?_⟩
  intro V
  change Module.Finite Γ(O.toScheme, V.1) Γ(O.toScheme, V.1)
  infer_instance

/-- The ideal of an effective Cartier divisor is finitely generated over every affine open. -/
lemma ideal_fg (hI : IsEffectiveCartierIdeal I) (U : X.affineOpens) : (I.ideal U).FG := by
  have h := hasFiniteAffineSections_kernelModule I hI U
  rw [← I.ker_subschemeι_app U]
  change Module.Finite Γ(X, U.1) (RingHom.ker (I.subschemeι.app U.1).hom) at h
  exact Module.Finite.iff_fg.1 h

/-- A closed subscheme whose ideal is finitely generated over every affine open is locally of
finite presentation. -/
lemma locallyOfFinitePresentation_subschemeι (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    LocallyOfFinitePresentation I.subschemeι := by
  -- Instance search does not find this instance here, so it is supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    I.subschemeCover.openCover fun (U : X.affineOpens) => ?_
  change LocallyOfFinitePresentation (I.subschemeCover.f U ≫ I.subschemeι)
  rw [I.subschemeCover_map_subschemeι,
    Scheme.IdealSheafData.glueDataObjι]
  have h1 : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    refine RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker]
    exact hI U
  have h2 : LocallyOfFinitePresentation U.2.isoSpec.inv :=
    locallyOfFinitePresentation_of_isOpenImmersion _
  have h3 : LocallyOfFinitePresentation U.1.ι := locallyOfFinitePresentation_of_isOpenImmersion _
  have h12 := locallyOfFinitePresentation_comp
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) U.2.isoSpec.inv
  exact @locallyOfFinitePresentation_comp _ _ _ _ _ h12 h3

/-- An effective Cartier divisor is a closed subscheme locally of finite presentation. -/
lemma locallyOfFinitePresentation_of_isEffectiveCartierIdeal (hI : IsEffectiveCartierIdeal I) :
    LocallyOfFinitePresentation I.subschemeι :=
  locallyOfFinitePresentation_subschemeι I (ideal_fg I hI)

end Cartier

section Families

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The comparison map `X ×_S T' ⟶ X ×_S T` over a morphism `T' ⟶ T` of `S`-schemes, as in the
statements. -/
abbrev mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    pullback f s' ⟶ pullback f s :=
  pullback.map f s' f s (𝟙 X) h (𝟙 _) (by simp) (by simp [w])

@[reassoc]
lemma mapX_fst {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    mapX f h w ≫ pullback.fst f s = pullback.fst f s' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma mapX_snd {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    mapX f h w ≫ pullback.snd f s = pullback.snd f s' ≫ h :=
  pullback.lift_snd _ _ _

lemma isPullback_mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    IsPullback (mapX f h w) (pullback.snd f s') (pullback.snd f s) h := by
  subst w
  refine IsPullback.of_right ?_ (mapX_snd f h rfl) (IsPullback.of_hasPullback f s)
  rw [mapX_fst]
  exact IsPullback.of_hasPullback f (h ≫ s)

lemma mapX_comp {T T' T'' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {s'' : T'' ⟶ S}
    (h : T' ⟶ T) (w : h ≫ s = s') (h' : T'' ⟶ T') (w' : h' ≫ s' = s'') :
    mapX f h' w' ≫ mapX f h w = mapX f (h' ≫ h) (by rw [Category.assoc, w, w']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mapX_fst, mapX_fst, mapX_fst]
  · rw [Category.assoc, mapX_snd, mapX_snd_assoc, mapX_snd]

lemma mapX_congr {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {h₁ h₂ : T' ⟶ T}
    (w₁ : h₁ ≫ s = s') (w₂ : h₂ ≫ s = s') (e : h₁ = h₂) : mapX f h₁ w₁ = mapX f h₂ w₂ := by
  subst e
  rfl

lemma mapX_id {T : Scheme.{u}} (s : T ⟶ S) : mapX f (𝟙 T) (Category.id_comp s) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mapX_fst, Category.id_comp]
  · rw [mapX_snd, Category.id_comp, Category.comp_id]

end Families

/-- Preimages of disjoint opens are disjoint. -/
lemma disjoint_preimage {X Y : Scheme.{u}} (φ : X ⟶ Y) {A B : Y.Opens} (h : Disjoint A B) :
    Disjoint (φ ⁻¹ᵁ A) (φ ⁻¹ᵁ B) := by
  rw [disjoint_iff] at h ⊢
  rw [← Scheme.Hom.preimage_inf, h, Scheme.Hom.preimage_bot]

/-- A morphism into an open subscheme lands in that open after composing with the inclusion. -/
lemma range_comp_ι_subset {T Y : Scheme.{u}} {U : Y.Opens} (g : T ⟶ U.toScheme) :
    Set.range (g ≫ U.ι).base ⊆ (U : Set Y) := by
  have : Set.range (g ≫ U.ι).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨g.base x, by rw [Scheme.Hom.comp_apply]⟩
  rwa [Scheme.Opens.range_ι] at this

/-- Main theorem: `HilbertSchemeUniversalFamilyStatement` and
`RelativeEffectiveCartierLocusStatement` imply `RelativeEffectiveDivisorHilbertPiecesStatement`. -/
theorem relativeEffectiveDivisorHilbertPiecesReduction :
    RelativeEffectiveDivisorHilbertPiecesReductionStatement.{u} := by
  intro hHGP hCLO A _ _ X f 𝓛X hf h𝓛 hci
  have : Flat f := hf
  -- `f` is proper, hence locally of finite presentation over the noetherian base.
  have hfprop : IsProper f := by
    obtain ⟨N, 𝔓, h𝔓⟩ := hci
    rw [← 𝔓.toProj_π]
    have : IsProper (ProjSpace.π A N) :=
      Langlands.AlgebraicGeometry.projectiveSpaceToSpec_isProper A N
    infer_instance
  have hflfp : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨H, πH, W, hπlfp, hπsep, hrep, UH, hUHdisj, hUHtop, hUH⟩ :=
    hHGP A f 𝓛X hf hflfp h𝓛 hci
  have hHln : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian πH
  -- The universal family over `H`.
  have hWflat : Flat (W.subschemeι ≫ pullback.snd f πH) := by
    have h := ((hrep H πH).1 (𝟙 H) (Category.id_comp _)).1
    have e : W.comap (mapX f (𝟙 H) (Category.id_comp πH)) = W := by
      rw [mapX_id, Scheme.IdealSheafData.comap_id]
    rwa [e] at h
  obtain ⟨U, hU⟩ := hCLO (pullback.snd f πH) W hHln inferInstance inferInstance hWflat
  -- The divisor scheme is the open Cartier locus `U` of the Hilbert scheme.
  let d : U.toScheme ⟶ Spec (CommRingCat.of A) := U.ι ≫ πH
  have hWD : IsRelativeEffectiveCartierIdeal (pullback.snd f d)
      (W.comap (mapX f U.ι (rfl : U.ι ≫ πH = d))) :=
    (hU U.ι _ _ (isPullback_mapX f U.ι rfl)).2 (by rw [Scheme.Opens.range_ι])
  have hcomap : ∀ {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of A)} (g : T ⟶ U.toScheme)
      (hg : g ≫ d = s),
      (W.comap (mapX f U.ι (rfl : U.ι ≫ πH = d))).comap (mapX f g hg) =
        W.comap (mapX f (g ≫ U.ι) (by rw [Category.assoc]; exact hg)) := by
    intro T s g hg
    rw [← Scheme.IdealSheafData.comap_comp, mapX_comp]
  refine ⟨U.toScheme, d, ⟨_, hWD⟩, inferInstance, inferInstance, fun T s => ⟨?_, ?_⟩, ?_⟩
  · -- Pulled-back divisors are relative effective Cartier divisors.
    intro g hg
    change IsRelativeEffectiveCartierIdeal (pullback.snd f s)
      ((W.comap (mapX f U.ι (rfl : U.ι ≫ πH = d))).comap (mapX f g hg))
    rw [hcomap g hg]
    exact (hU (g ≫ U.ι) _ _ (isPullback_mapX f (g ≫ U.ι) _)).2 (range_comp_ι_subset g)
  · -- Every relative effective divisor is classified by a unique point of `U`.
    intro I hI
    have hlfp : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s) := by
      have := locallyOfFinitePresentation_of_isEffectiveCartierIdeal I hI.1
      infer_instance
    obtain ⟨g, ⟨hg, hgI⟩, huniq⟩ := (hrep T s).2 I hI.2 hlfp
    have hgU : Set.range g.base ⊆ (U : Set H) := by
      refine (hU g _ _ (isPullback_mapX f g hg)).1 ?_
      rw [hgI]
      exact hI
    let g' : T ⟶ U.toScheme :=
      IsOpenImmersion.lift U.ι g (by rw [Scheme.Opens.range_ι]; exact hgU)
    have hg' : g' ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
    have hg'd : g' ≫ d = s := by
      change g' ≫ U.ι ≫ πH = s
      rw [← Category.assoc, hg', hg]
    refine ⟨g', ⟨hg'd, ?_⟩, ?_⟩
    · change (W.comap (mapX f U.ι (rfl : U.ι ≫ πH = d))).comap (mapX f g' hg'd) = I
      rw [hcomap g' hg'd, mapX_congr f _ hg hg']
      exact hgI
    · rintro g'' ⟨hg'', hg''I⟩
      have h1 : g'' ≫ U.ι = g := by
        refine huniq (g'' ≫ U.ι) ⟨by rw [Category.assoc]; exact hg'', ?_⟩
        rw [← hcomap g'' hg'']
        exact hg''I
      exact (cancel_mono U.ι).1 (h1.trans hg'.symm)
  · -- The Hilbert-polynomial pieces of the divisor scheme.
    refine ⟨fun θ => U.ι ⁻¹ᵁ UH θ, fun θ θ' hne => disjoint_preimage U.ι (hUHdisj hne), ?_,
      fun θ => ⟨?_, ?_⟩⟩
    · rw [← Scheme.Hom.preimage_iSup, hUHtop, Scheme.Hom.preimage_top]
    · -- H-quasi-projectivity.
      obtain ⟨n, c, hc, hcπ⟩ := (hUH θ).1
      have hrange : Set.range ((U.ι ⁻¹ᵁ UH θ).ι ≫ U.ι).base ⊆ Set.range (UH θ).ι.base := by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact x.2
      let j : (U.ι ⁻¹ᵁ UH θ).toScheme ⟶ (UH θ).toScheme :=
        IsOpenImmersion.lift (UH θ).ι ((U.ι ⁻¹ᵁ UH θ).ι ≫ U.ι) hrange
      have hj : j ≫ (UH θ).ι = (U.ι ⁻¹ᵁ UH θ).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
      have : IsOpenImmersion j := by
        have : IsOpenImmersion (j ≫ (UH θ).ι) := by rw [hj]; infer_instance
        exact IsOpenImmersion.of_comp j (UH θ).ι
      -- The piece `UH θ` is a noetherian scheme.
      have : IsProper ((UH θ).ι ≫ πH) := (hUH θ).1.isProper
      have : CompactSpace (UH θ).toScheme :=
        QuasiCompact.compactSpace_of_compactSpace ((UH θ).ι ≫ πH)
      have : IsNoetherian (UH θ).toScheme := {}
      have : NoetherianSpace (U.ι ⁻¹ᵁ UH θ).toScheme :=
        j.isOpenEmbedding.isInducing.noetherianSpace
      have : IsClosedImmersion c := hc
      refine ⟨n, j ≫ c, inferInstance, inferInstance, ?_⟩
      rw [Category.assoc, hcπ, ← Category.assoc, hj, Category.assoc]
    · -- The Hilbert-polynomial condition.
      intro B _ s g hg I hgI
      have hgU : (g ≫ U.ι) ≫ πH = s := by rw [Category.assoc]; exact hg
      have hI' : W.comap (mapX f (g ≫ U.ι) hgU) = I := by
        rw [← hcomap g hg]
        exact hgI
      rw [← (hUH θ).2 B s (g ≫ U.ι) hgU I hI']
      constructor
      · rintro h _ ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply]
        exact h ⟨x, rfl⟩
      · rintro h _ ⟨x, rfl⟩
        have hx := h ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply] at hx
        exact hx

end Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReduction
