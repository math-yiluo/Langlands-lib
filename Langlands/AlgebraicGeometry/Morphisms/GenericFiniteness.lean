/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Adapted by Worker 1001 from Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2, files
P2M/Sol/S_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes.lean,
P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes.lean
and P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType.lean.
Changes: the declarations are moved out of the P2M wrapper namespaces into
`Langlands.AlgebraicGeometry.GenericFiniteness`, and the solution theorems are renamed; the P2M
`open`/`export` commands are replaced by ordinary `open` commands; `P2M.Util` is not imported;
small elaboration adjustments for the project Mathlib. The paired Markdown file lists the changes.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Generic finiteness of quasi-finite morphisms at minimal primes

A quasi-finite morphism of finite type is finite over a basic open neighbourhood of every
minimal prime of an affine base, provided it is separated and quasi-compact.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.GenericFiniteness

section Ring

open Polynomial TensorProduct

theorem isIntegral_of_isLocalRing_of_forall_isNilpotent
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [Algebra.QuasiFinite R S]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal R, IsNilpotent x) : Algebra.IsIntegral R S := by
  classical
  set I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hI

  let e : (IsLocalRing.maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ I :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (IsLocalRing.maximalIdeal R)).symm.restrictScalars R)
  have : Module.Finite R (S ⧸ I) :=
    have : Module.Finite R ((IsLocalRing.maximalIdeal R).Fiber S) :=
      .trans (IsLocalRing.maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  have hInil : I ≤ nilradical S := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_nilradical.mpr ((h x hx).map (algebraMap R S))
  refine ⟨fun x => ?_⟩
  obtain ⟨F, hFm, hF⟩ : IsIntegral R (Ideal.Quotient.mkₐ R I x) := Algebra.IsIntegral.isIntegral _
  have hx : aeval x F ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply,
      aeval_def]
    exact hF
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hInil hx)
  exact ⟨F ^ n, hFm.pow n, by rw [← aeval_def, map_pow, hn]⟩

theorem exists_not_mem_isIntegral_smul
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.QuasiFinite R A]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) (a : A) :
    ∃ t : R, t ∉ p ∧ IsIntegral R (t • a) := by
  classical
  have hpI : p.IsPrime := hp.1.1
  let Rp := Localization.AtPrime p
  let S := Rp ⊗[R] A

  have hnil : ∀ x ∈ IsLocalRing.maximalIdeal Rp, IsNilpotent x := by
    intro x hx
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Rp) p ⊥ hp
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, ← hrad, Ideal.map_bot,
      Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by simpa using hn⟩
  have : Algebra.IsIntegral Rp S := isIntegral_of_isLocalRing_of_forall_isNilpotent hnil
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl
    (Rₘ := Rp) ((1 : Rp) ⊗ₜ[R] a : S) (Algebra.IsIntegral.isIntegral _)
  obtain ⟨G, hGm, hG⟩ := hm
  have h1 : (m • ((1 : Rp) ⊗ₜ[R] a) : S) = Algebra.TensorProduct.includeRight ((m : R) • a) := by
    rw [Algebra.TensorProduct.includeRight_apply, Submonoid.smul_def, TensorProduct.tmul_smul]
  have h2 : (TensorProduct.mk R Rp A 1) (aeval ((m : R) • a) G) = 0 := by
    rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply,
      ← h1, aeval_def]
    exact hG
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl (TensorProduct.mk R Rp A 1)).mp h2
  refine ⟨s * m, fun h => (hpI.mem_or_mem h).elim s.2 m.2, ?_⟩
  have h3 : aeval ((m : R) • a) (C (s : R) * G) = 0 := by
    rw [map_mul, aeval_C, ← Algebra.smul_def, ← Submonoid.smul_def]
    exact hs
  have := isIntegral_leadingCoeff_smul (C (s : R) * G) ((m : R) • a) h3
  rwa [leadingCoeff_mul_monic hGm, leadingCoeff_C, smul_smul] at this

theorem finite_awayMap_of_forall_isIntegral_smul
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (gens : Finset A) (hgens : Algebra.adjoin R (gens : Set A) = ⊤)
    (t : A → R) (ht : ∀ a ∈ gens, IsIntegral R (t a • a)) :
    (Localization.awayMap (algebraMap R A) (∏ a ∈ gens, t a)).Finite := by
  classical
  set r : R := ∏ a ∈ gens, t a with hr
  let Rr := Localization.Away r
  let Ar := Localization.Away (algebraMap R A r)
  let φ : Rr →+* Ar := Localization.awayMap (algebraMap R A) r
  let : Algebra Rr Ar := φ.toAlgebra
  have : IsScalarTower R Rr Ar := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R A Ar]
    exact (IsLocalization.map_eq _ x).symm
  have : Algebra.FiniteType R A := ⟨⟨gens, hgens⟩⟩
  have hft : φ.FiniteType :=
    RingHom.localization_away_map_finiteType R A Rr Ar (algebraMap R A) r
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let ψ : A →ₐ[R] Ar := IsScalarTower.toAlgHom R A Ar
  have hr_unit : IsUnit (algebraMap R Rr r) := IsLocalization.Away.algebraMap_isUnit r

  have hgen : ∀ a ∈ gens, IsIntegral Rr (ψ a) := by
    intro a ha
    have hu : IsUnit (algebraMap R Rr (t a)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem t ha)) hr_unit
    obtain ⟨u, hu'⟩ := hu
    have h1 : IsIntegral Rr (algebraMap Rr Ar (algebraMap R Rr (t a)) * ψ a) := by
      have := (ht a ha).map ψ
      rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R Rr Ar] at this
      exact this.tower_top
    have h2 : ψ a = algebraMap Rr Ar ↑u⁻¹ * (algebraMap Rr Ar (algebraMap R Rr (t a)) * ψ a) := by
      rw [← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul]
    rw [h2]
    exact isIntegral_algebraMap.mul h1

  have hA : ∀ a : A, IsIntegral Rr (ψ a) := by
    have hle : Algebra.adjoin R (ψ '' (gens : Set A)) ≤
        (integralClosure Rr Ar).restrictScalars R := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨a, ha, rfl⟩
      exact (Subalgebra.mem_restrictScalars R).mpr (hgen a ha)
    intro a
    have ha : ψ a ∈ Algebra.adjoin R (ψ '' (gens : Set A)) := by
      rw [← AlgHom.map_adjoin, hgens]
      exact Subalgebra.mem_map.mpr ⟨a, Algebra.mem_top, rfl⟩
    exact (Subalgebra.mem_restrictScalars R).mp (hle ha)

  have hint : φ.IsIntegral := by
    intro x
    change IsIntegral Rr x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap R A r)) x
    change _root_.IsIntegral Rr (IsLocalization.mk' Ar a s)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hu : IsUnit (algebraMap R Rr (r ^ n)) := by rw [map_pow]; exact hr_unit.pow n
    obtain ⟨u, hu'⟩ := hu
    have hx : IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u = ψ a := by
      rw [hu', ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A Ar, map_pow, hn]
      exact IsLocalization.mk'_spec Ar a s
    have key : IsIntegral Rr (IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u) := by
      rw [hx]; exact hA a
    have : IsLocalization.mk' Ar a s =
        algebraMap Rr Ar ↑u⁻¹ * (IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u) := by
      rw [mul_comm (IsLocalization.mk' Ar a s), ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    rw [this]
    exact isIntegral_algebraMap.mul key
  exact hint.to_finite hft


theorem exists_not_mem_finite_awayMap_of_mem_minimalPrimes
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [Algebra.QuasiFinite R A]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ (Localization.awayMap (algebraMap R A) r).Finite := by
  classical
  have hpI : p.IsPrime := hp.1.1
  obtain ⟨gens, hgens⟩ := ‹Algebra.FiniteType R A›
  choose t ht hti using fun a : A => exists_not_mem_isIntegral_smul p hp a
  refine ⟨∏ a ∈ gens, t a, ?_, finite_awayMap_of_forall_isIntegral_smul gens hgens t
    fun a _ => hti a⟩
  rw [hpI.prod_mem_iff]
  simpa using fun a (_ : a ∈ gens) => ht a

end Ring

section Scheme

set_option backward.isDefEq.respectTransparency.types false

theorem isFinite_ι_of_isClosed {X : Scheme.{u}} (W : X.Opens) (hW : IsClosed (W : Set X)) : IsFinite W.ι := by
  have : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion W.ι (by rw [Scheme.Opens.range_ι]; exact hW)
  infer_instance


theorem IsFinite.of_forall_isClosed_of_iSup_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (U : Fin n → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hcl : ∀ i, IsClosed ((U i : Set X))) (hfin : ∀ i, IsFinite ((U i).ι ≫ f)) :
    IsFinite f := by
  induction n generalizing X with
  | zero =>
    have : IsEmpty X := ⟨fun x => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hU, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, -⟩ := hx
      exact Fin.elim0 i⟩
    infer_instance
  | succ n ih =>

    let V : X.Opens := U 0
    let W : X.Opens := ⟨(V : Set X)ᶜ, (hcl 0).isOpen_compl⟩
    have hWcl : IsClosed (W : Set X) := by
      show IsClosed (V : Set X)ᶜ
      exact (U 0).2.isClosed_compl
    have hVW : IsCompl V.ι.opensRange W.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
      refine IsCompl.of_eq ?_ ?_
      · apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot]
        exact Set.inter_compl_self _
      · apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top]
        exact Set.union_compl_self _
    obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V.ι W.ι hVW

    have hV : IsFinite (V.ι ≫ f) := hfin 0
    have hW : IsFinite (W.ι ≫ f) := by
      have : IsFinite W.ι := isFinite_ι_of_isClosed W hWcl
      refine ih (W.ι ≫ f) (fun i => W.ι ⁻¹ᵁ U i.succ) ?_ ?_ ?_
      ·
        refine top_le_iff.mp fun w _ => ?_
        have hw : W.ι.base w ∈ (⊤ : X.Opens) := trivial
        rw [← hU, TopologicalSpace.Opens.mem_iSup] at hw
        obtain ⟨i, hi⟩ := hw
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exfalso
          have : W.ι.base w ∈ (W : Set X) := by rw [← Scheme.Opens.range_ι W]; exact ⟨w, rfl⟩
          exact this hi
        · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hi⟩
      · intro i
        exact (hcl i.succ).preimage W.ι.continuous
      · intro i
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
        have := hfin i.succ
        infer_instance

    let e := hc.coconePointUniqueUpToIso (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u}))
    have hVι : V.ι ≫ e.hom = coprod.inl := by
      have h__af := (hc.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u})) ⟨WalkingPair.left⟩)
      simp at h__af
      exact h__af
    have hWι : W.ι ≫ e.hom = coprod.inr := by
      have h__af := (hc.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u})) ⟨WalkingPair.right⟩)
      simp at h__af
      exact h__af
    have hdesc : e.inv ≫ f = coprod.desc (V.ι ≫ f) (W.ι ≫ f) := by
      apply coprod.hom_ext
      · rw [coprod.inl_desc, ← hVι]; erw [Category.assoc, e.hom_inv_id_assoc]
      · rw [coprod.inr_desc, ← hWι]; erw [Category.assoc, e.hom_inv_id_assoc]
    have h1 : IsFinite (coprod.desc (V.ι ≫ f) (W.ι ≫ f)) := inferInstance
    have h2 : IsFinite (e.hom : X ⟶ (V : Scheme.{u}) ⨿ (W : Scheme.{u})) := inferInstance
    have h3 : IsFinite ((e.hom : X ⟶ (V : Scheme.{u}) ⨿ (W : Scheme.{u})) ≫ coprod.desc (V.ι ≫ f) (W.ι ≫ f)) :=
      MorphismProperty.comp_mem @_root_.AlgebraicGeometry.IsFinite _ _ h2 h1
    rw [← hdesc, e.hom_inv_id_assoc] at h3
    exact h3


theorem exists_isFinite_restrict_chart {R : Type u} [CommRing R] {A : CommRingCat.{u}}
    (φ : CommRingCat.of R ⟶ A) (hft : φ.hom.FiniteType) (hqf : φ.hom.QuasiFinite)
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ ∀ s : R, IsFinite (Spec.map φ ∣_ PrimeSpectrum.basicOpen (r * s)) := by
  let D : R → (Spec (CommRingCat.of R)).Opens := fun t => PrimeSpectrum.basicOpen t
  algebraize [φ.hom]
  obtain ⟨r, hr, hfin⟩ := exists_not_mem_finite_awayMap_of_mem_minimalPrimes (A := A) p hp
  refine ⟨r, hr, fun s => ?_⟩

  have h1 : IsFinite (Spec.map φ ∣_ PrimeSpectrum.basicOpen r) := by
    refine (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite (SpecMapRestrictBasicOpenIso φ r)).mpr ?_
    exact (IsFinite.SpecMap_iff _).mpr hfin

  have hle : PrimeSpectrum.basicOpen (r * s) ≤ PrimeSpectrum.basicOpen r := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have h2 := IsZariskiLocalAtTarget.restrict h1 ((D r).ι ⁻¹ᵁ D (r * s))
  have h3 := (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite
    (morphismRestrictRestrict (Spec.map φ) (D r) ((D r).ι ⁻¹ᵁ D (r * s)))).mp h2
  have heq : (D r).ι ''ᵁ ((D r).ι ⁻¹ᵁ D (r * s)) = D (r * s) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  exact (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite (morphismRestrictEq (Spec.map φ) heq)).mp h3

theorem exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ IsFinite (f ∣_ PrimeSpectrum.basicOpen r) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have hA : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i => by
    show IsAffine (X.affineCover.X _); infer_instance

  let c : ∀ i : 𝒰.I₀, Spec (Γ(𝒰.X i, ⊤)) ⟶ X := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  have hc : ∀ i, IsOpenImmersion (c i) := fun i => inferInstance
  have hchart : ∀ i : 𝒰.I₀, ∃ r : R, r ∉ p ∧ ∀ s : R, IsFinite ((c i ≫ f) ∣_ PrimeSpectrum.basicOpen (r * s)) := by
    intro i
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (c i ≫ f)
    have hft : φ.hom.FiniteType := by
      have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    have hqf : φ.hom.QuasiFinite := by
      have : LocallyQuasiFinite (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    obtain ⟨r, hr, h⟩ := exists_isFinite_restrict_chart φ hft hqf p hp
    exact ⟨r, hr, fun s => by have := h s; rwa [hφ] at this⟩
  choose rr hrr hfinr using hchart
  have hprime : p.IsPrime := hp.1.1
  refine ⟨∏ i, rr i, (hprime.prod_mem_iff.not.mpr (by simpa using hrr)), ?_⟩
  set r := ∏ i, rr i with hr
  set V : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r

  let h : ∀ i : 𝒰.I₀, ((c i) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ (f ⁻¹ᵁ V).toScheme := fun i => (c i) ∣_ (f ⁻¹ᵁ V)
  have hfin : ∀ i, IsFinite (h i ≫ f ∣_ V) := by
    intro i
    rw [← morphismRestrict_comp]
    have : r = rr i * ∏ j ∈ Finset.univ.erase i, rr j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [show V = PrimeSpectrum.basicOpen (rr i * ∏ j ∈ Finset.univ.erase i, rr j) by rw [← this]]
    exact hfinr i _

  have hclosed : ∀ i, IsClosed (Set.range (h i)) := by
    intro i
    have : IsProper (h i) := IsProper.of_comp (h i) (f ∣_ V)
    exact (h i).isClosedMap.isClosed_range

  let U : 𝒰.I₀ → (f ⁻¹ᵁ V).toScheme.Opens := fun i => (h i).opensRange
  have hcov : ⨆ i, U i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    set j := 𝒰.idx ((f ⁻¹ᵁ V).ι x) with hj
    obtain ⟨y, hy⟩ : ∃ y, 𝒰.f j y = (f ⁻¹ᵁ V).ι x := 𝒰.covers ((f ⁻¹ᵁ V).ι x)
    have hy' : c j ((𝒰.X j).isoSpec.hom y) = (f ⁻¹ᵁ V).ι x := by
      calc c j ((𝒰.X j).isoSpec.hom y) = ((𝒰.X j).isoSpec.hom ≫ c j) y := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (𝒰.f j) y := by simp only [c, Iso.hom_inv_id_assoc]
        _ = (f ⁻¹ᵁ V).ι x := hy
    have hyV : (𝒰.X j).isoSpec.hom y ∈ (c j) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
      show c j _ ∈ f ⁻¹ᵁ V
      rw [hy']; exact x.2
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ⟨⟨_, hyV⟩, ?_⟩⟩
    apply (f ⁻¹ᵁ V).ι.injective
    have e1 : (f ⁻¹ᵁ V).ι ((h j) ⟨_, hyV⟩) = (h j ≫ (f ⁻¹ᵁ V).ι) ⟨_, hyV⟩ :=
      (Scheme.Hom.comp_apply _ _ _).symm
    rw [e1, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact hy'
  have hUfin : ∀ i, IsFinite ((U i).ι ≫ f ∣_ V) := by
    intro i
    rw [← Scheme.Hom.isoOpensRange_inv_comp (h i), Category.assoc]
    infer_instance

  let e := (Fintype.equivFin 𝒰.I₀).symm
  refine IsFinite.of_forall_isClosed_of_iSup_eq_top (f ∣_ V) (U ∘ e) ?_ (fun k => hclosed (e k))
    (fun k => hUfin (e k))
  rw [← hcov]
  exact (Function.Surjective.iSup_comp e.surjective U)


/-- A formally unramified morphism locally of finite type is locally quasi-finite.
(Adapted from Anthropic FLT, `P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType.lean`.) -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hu : (f.appLE U V e).hom.FormallyUnramified := f.formallyUnramified_appLE hU hV e
  have hft : (f.appLE U V e).hom.FiniteType := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

end Scheme

end Langlands.AlgebraicGeometry.GenericFiniteness
