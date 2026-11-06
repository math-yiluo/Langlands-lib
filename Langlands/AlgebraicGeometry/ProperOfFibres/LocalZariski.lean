import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop

/-! # Properness over a noetherian local normal domain from an open embedding into a proper scheme -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProperOfFibres

variable {B : Type u} [CommRing B] [IsLocalRing B]

/-- A ring map is injective on global sections of spectra exactly when it is injective. -/
theorem SpecMap_appTop_injective {R S : Type u} [CommRing R] [CommRing S] (ψ : R →+* S)
    (hψ : Function.Injective ψ) :
    Function.Injective (Spec.map (CommRingCat.ofHom ψ)).appTop := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  intro a b hab
  have : (Scheme.ΓSpecIso (CommRingCat.of R)).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom b := by
    apply hψ
    have h' := congrArg (fun F => F.hom) h
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h'
    have ha := congrArg (fun F => F a) h'
    have hb := congrArg (fun F => F b) h'
    simp only [RingHom.coe_comp, Function.comp_apply] at ha hb
    rw [← ha, ← hb, hab]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1 this

/-- The image of the residue-field point is the closed point. -/
theorem range_SpecMap_residue :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) =
      {IsLocalRing.closedPoint B} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint (IsLocalRing.ResidueField B) :=
      Subsingleton.elim _ _
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField B),
      IsLocalRing.comap_closedPoint (IsLocalRing.residue B)⟩

/-- The zero ideal of `B` lies in the image of the spectrum of a fraction field. -/
theorem bot_mem_range_SpecMap_algebraMap [IsDomain B] (K : Type u) [Field K] [Algebra B K]
    [IsFractionRing B K] :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap B K))) := by
  refine ⟨IsLocalRing.closedPoint K, ?_⟩
  change PrimeSpectrum.comap (algebraMap B K) (IsLocalRing.closedPoint K) = _
  ext1
  rw [PrimeSpectrum.comap_asIdeal]
  have : (IsLocalRing.closedPoint K).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [this]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective B K)

/-- A nonempty closed subset of the spectrum of a local ring contains the closed point. -/
theorem closedPoint_mem_of_isClosed {Z : Set (PrimeSpectrum B)} (hZ : IsClosed Z)
    (hne : Z.Nonempty) : IsLocalRing.closedPoint B ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  exact (IsLocalRing.specializes_closedPoint z).mem_closed hZ hz

/-- **Local Zariski properness.** Let `B` be a noetherian local normal domain with fraction
field `K`. A flat quasi-compact `B`-scheme `X` with an open immersion into a proper `B`-scheme,
whose generic fibre has global sections `K` and whose closed fibre is proper and nonempty, is
proper over `B`. -/
theorem isProper_of_isOpenImmersion [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]
    {X W : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [Flat f] [QuasiCompact f]
    (ι : X ⟶ W) [IsOpenImmersion ι] (g : W ⟶ Spec (CommRingCat.of B)) [IsProper g]
    (hfac : ι ≫ g = f)
    (hK : Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B K)))).appTop)
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))))]
    [Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))))] :
    IsProper f := by
  set φK := Spec.map (CommRingCat.ofHom (algebraMap B K)) with hφK
  set ψ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) with hψ
  -- the generic fibre, mapped to `W`, and its scheme-theoretic image
  let h : pullback f φK ⟶ W := pullback.fst f φK ≫ ι
  have hhg : h ≫ g = pullback.snd f φK ≫ φK := by
    simp only [h, Category.assoc, hfac, pullback.condition]
  have : QuasiCompact (h ≫ g) := by rw [hhg]; infer_instance
  have : QuasiCompact h := QuasiCompact.of_comp h g
  let i := h.imageι
  let q := i ≫ g
  have hq : h.toImage ≫ q = pullback.snd f φK ≫ φK := by
    simp only [q, i, Scheme.Hom.toImage_imageι_assoc, hhg]
  -- global sections of the image
  have hqΓ : Function.Bijective q.appTop := by
    have hcomp : q.appTop ≫ h.toImage.appTop = φK.appTop ≫ (pullback.snd f φK).appTop := by
      rw [← Scheme.Hom.comp_appTop, hq, Scheme.Hom.comp_appTop]
    have hinjZ : Function.Injective h.toImage.appTop :=
      TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := h.image.sheaf)
        h.toImage.c ⊤ (fun x _ ↦ h.stalkFunctor_toImage_injective x)
    let eB := Scheme.ΓSpecIso (CommRingCat.of B)
    let eK := Scheme.ΓSpecIso (CommRingCat.of K)
    let γ := RingEquiv.ofBijective (pullback.snd f φK).appTop.hom hK
    let τ : Γ(h.image, ⊤) →+* K :=
      eK.hom.hom.comp (γ.symm.toRingHom.comp h.toImage.appTop.hom)
    have hτinj : Function.Injective τ :=
      (ConcreteCategory.bijective_of_isIso eK.hom).1.comp (γ.symm.injective.comp hinjZ)
    have hτ : ∀ b, τ (q.appTop b) = algebraMap B K (eB.hom b) := by
      intro b
      have h1 : h.toImage.appTop (q.appTop b) = (pullback.snd f φK).appTop (φK.appTop b) := by
        have := congrArg (fun F ↦ F.hom b) hcomp
        simpa using this
      have h2 : eK.hom (φK.appTop b) = algebraMap B K (eB.hom b) :=
        congrArg (fun F ↦ F.hom b)
          (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap B K)))
      have h3 : γ.symm ((pullback.snd f φK).appTop (φK.appTop b)) = φK.appTop b :=
        γ.symm_apply_apply _
      simp only [τ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [h1, h3, h2]
    refine ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
    · have := congrArg τ hab
      rw [hτ, hτ] at this
      exact (ConcreteCategory.bijective_of_isIso eB.hom).1
        (IsFractionRing.injective B K this)
    · have hint : q.appTop.hom.IsIntegral := isIntegral_appTop_of_universallyClosed q
      obtain ⟨p, hp, hpz⟩ := (hint z).map τ
      have hcompτ : τ.comp q.appTop.hom = (algebraMap B K).comp eB.hom.hom :=
        RingHom.ext hτ
      rw [hcompτ] at hpz
      have hzint : IsIntegral B (τ z) :=
        ⟨p.map eB.hom.hom, hp.map _, by rw [Polynomial.eval₂_map]; exact hpz⟩
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
      refine ⟨eB.inv y, hτinj ?_⟩
      rw [hτ, ← hy]
      congr 1
      exact congrArg (fun F ↦ F.hom y) eB.inv_hom_id
  have hF := isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop q hqΓ
  set s := IsLocalRing.closedPoint B with hs
  -- the image of `X` lies in the scheme-theoretic image of the generic fibre
  have hrange_i : Set.range i = closure (Set.range h) := by
    simp only [i, Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker]
  have hιi : Set.range ι ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    have hy : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ⤳ f x :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp bot_le)
    obtain ⟨x', hx'x, hx'⟩ := Flat.generalizingMap f hy
    have hx'r : x' ∈ Set.range (pullback.fst f φK) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx']
      exact bot_mem_range_SpecMap_algebraMap K
    obtain ⟨w, rfl⟩ := hx'r
    rw [hrange_i]
    have hsp : ι (pullback.fst f φK w) ⤳ ι x := hx'x.map ι.continuous
    have hw : ι (pullback.fst f φK w) ∈ Set.range h := ⟨w, rfl⟩
    exact closure_mono (Set.singleton_subset_iff.mpr hw) hsp.mem_closure
  -- the closed fibre of `X` has closed image in `W`
  have : IsClosedImmersion ψ :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let e : pullback f ψ ⟶ W := pullback.fst f ψ ≫ ι
  have : IsProper (e ≫ g) := by
    rw [show e ≫ g = pullback.snd f ψ ≫ ψ by simp only [e, Category.assoc, hfac,
      pullback.condition]]
    infer_instance
  have : IsProper e := IsProper.of_comp e g
  have hE : IsClosed (Set.range e) := e.isClosedMap.isClosed_range
  have hEι : Set.range e ⊆ Set.range ι := by
    rintro _ ⟨w, rfl⟩
    exact ⟨pullback.fst f ψ w, rfl⟩
  have hEmem : ∀ x, f x = s → ι x ∈ Set.range e := by
    intro x hx
    have hxr : x ∈ Set.range (pullback.fst f ψ) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx, hψ, range_SpecMap_residue]
      rfl
    obtain ⟨w, rfl⟩ := hxr
    exact ⟨w, rfl⟩
  have hqi : ∀ z, q z = g (i z) := fun z ↦ rfl
  have hgι : ∀ x, g (ι x) = f x := fun x ↦ by rw [← hfac]; rfl
  -- the closed fibre of the image lies in the image of `X`
  have hFU : ∀ z, q z = s → i z ∈ Set.range ι := by
    have hU : IsOpen (i ⁻¹' Set.range ι) :=
      ι.isOpenEmbedding.isOpen_range.preimage i.continuous
    have hcover : q ⁻¹' {s} ⊆ i ⁻¹' Set.range e ∪ (i ⁻¹' Set.range ι)ᶜ := by
      intro z hz
      by_cases hzι : i z ∈ Set.range ι
      · obtain ⟨x, hx⟩ := hzι
        left
        show i z ∈ Set.range e
        rw [← hx]
        apply hEmem
        rw [← hgι, hx, ← hqi]
        exact hz
      · exact Or.inr hzι
    have hdisj : q ⁻¹' {s} ∩ (i ⁻¹' Set.range e ∩ (i ⁻¹' Set.range ι)ᶜ) = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
        iff_false, not_and, not_not]
      intro _ hze
      exact hEι hze
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hF) (i ⁻¹' Set.range e)
        (i ⁻¹' Set.range ι)ᶜ (hE.preimage i.continuous) hU.isClosed_compl hcover hdisj with hu | hv
    · exact fun z hz ↦ hEι (hu hz)
    · exfalso
      obtain ⟨w⟩ := ‹Nonempty ↥(pullback f ψ)›
      have hfx : f (pullback.fst f ψ w) = s := by
        have : f (pullback.fst f ψ w) = ψ (pullback.snd f ψ w) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        rw [this]
        have hmem : ψ (pullback.snd f ψ w) ∈ Set.range ψ := ⟨_, rfl⟩
        have hr : Set.range ψ = {s} := range_SpecMap_residue
        rw [hr] at hmem
        exact hmem
      obtain ⟨z, hz⟩ := hιi ⟨pullback.fst f ψ w, rfl⟩
      have hzF : z ∈ q ⁻¹' {s} := by
        show q z = s
        rw [hqi, hz, hgι, hfx]
      exact hv hzF ⟨_, hz.symm⟩
  -- hence the whole image lies in the image of `X`
  have hiι : Set.range i ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    by_contra hz
    have hC : IsClosed (q '' (i ⁻¹' Set.range ι)ᶜ) :=
      q.isClosedMap _ ((ι.isOpenEmbedding.isOpen_range.preimage i.continuous).isClosed_compl)
    obtain ⟨z', hz'C, hz's⟩ := closedPoint_mem_of_isClosed hC ⟨q z, z, hz, rfl⟩
    exact hz'C (hFU z' hz's)
  have hclosed : IsClosed (Set.range ι) := by
    rw [show Set.range ι = Set.range i from subset_antisymm hιi hiι]
    exact i.isClosedEmbedding.isClosed_range
  have : IsClosedImmersion ι := IsClosedImmersion.of_isPreimmersion ι hclosed
  rw [← hfac]
  infer_instance

end Langlands.AlgebraicGeometry.ProperOfFibres
