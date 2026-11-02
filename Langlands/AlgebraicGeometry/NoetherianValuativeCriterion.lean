import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one
import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Langlands.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional

/-! # Discrete valuation ring criterion for universal closedness over a noetherian affine base

A quasi-compact morphism `f : X ⟶ Spec R` locally of finite type over a noetherian ring `R` is
universally closed as soon as every valuative square of `f` whose valuation ring is a discrete
valuation ring has a lift.

The proof adapts the Anthropic FLT proof of the analogous criterion over rings of finite type over
`ℤ` (FLT module `P2M/Sol/S_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift`
and its two FLT dependencies for valuative squares and for discrete valuation rings in finite
extensions); the paired Markdown file lists the changes. Copyright 2026 Anthropic, PBC, licensed
under the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Topology

namespace Langlands.AlgebraicGeometry

universe u v w

namespace NoetherianValuativeCriterion

/-- A morphism locally of finite type to the spectrum of a noetherian ring is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_of_isNoetherianRing {C : Type u} [CommRing C]
    [IsNoetherianRing C] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C))
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation g := by
  have : IsNoetherianRing ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    isNoetherianRing_of_ringEquiv C
      (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv
  refine HasRingHomProperty.of_source_openCover (P := @LocallyOfFinitePresentation)
    X.affineCover fun i => ?_
  have hft : ((X.affineCover.f i ≫ g).appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  exact RingHom.FinitePresentation.of_finiteType.mp hft

/-- Lifts for valuative squares with a discrete valuation ring pass to base changes. -/
theorem hasLift_baseChange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {iX : X' ⟶ X} {iY : Y' ⟶ Y} (hP : IsPullback iX f' f iY)
    (H : ∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R → S.commSq.HasLift)
    (S : ValuativeCommSq f') (hS : IsDiscreteValuationRing S.R) : S.commSq.HasLift := by
  let S' : ValuativeCommSq f :=
    { R := S.R
      K := S.K
      i₁ := S.i₁ ≫ iX
      i₂ := S.i₂ ≫ iY
      commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% S.commSq.w]⟩ }
  obtain ⟨l₀, hl₁, hl₂⟩ := (H S' hS).exists_lift
  refine ⟨⟨⟨hP.lift l₀ S.i₂ (by simpa [S'] using hl₂), ?_, hP.lift_snd _ _ _⟩⟩⟩
  apply hP.hom_ext
  · simpa [S'] using hl₁
  · simp only [Category.assoc]
    rw [hP.lift_snd, S.commSq.w]

/-- Every point `x` of a constructible set `s` has an open neighbourhood `U` with
`U ∩ closure {x} ⊆ s`. -/
theorem exists_isOpen_inter_closure_subset {T : Type u} [TopologicalSpace T] {s : Set T}
    (hs : IsConstructible s) :
    ∀ x ∈ s, ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ s := by
  let Q : Set T → Prop := fun s => ∀ x ∈ s, ∃ U : Set T, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ s
  have hQi : ∀ s t, Q s → Q t → Q (s ∩ t) := by
    intro s t hs ht x ⟨hxs, hxt⟩
    obtain ⟨U, hU, hxU, hUs⟩ := hs x hxs
    obtain ⟨V, hV, hxV, hVt⟩ := ht x hxt
    exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
      fun y ⟨⟨hyU, hyV⟩, hy⟩ => ⟨hUs ⟨hyU, hy⟩, hVt ⟨hyV, hy⟩⟩⟩
  have hQu : ∀ s t, Q s → Q t → Q (s ∪ t) := by
    intro s t hs ht x hx
    rcases hx with hxs | hxt
    · obtain ⟨U, hU, hxU, hUs⟩ := hs x hxs
      exact ⟨U, hU, hxU, fun y hy => Or.inl (hUs hy)⟩
    · obtain ⟨V, hV, hxV, hVt⟩ := ht x hxt
      exact ⟨V, hV, hxV, fun y hy => Or.inr (hVt hy)⟩
  suffices h : Q s ∧ Q sᶜ from h.1
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨fun x hx => ⟨U, hU, hx, fun y hy => hy.1⟩,
      fun x hx => ⟨Set.univ, isOpen_univ, trivial, ?_⟩⟩
    rintro y ⟨-, hy⟩
    exact (hU.isClosed_compl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)) hy
  | union s hs t ht ihs iht =>
    exact ⟨hQu _ _ ihs.1 iht.1, by rw [Set.compl_union]; exact hQi _ _ ihs.2 iht.2⟩
  | compl s hs ih => exact ⟨ih.2, by rw [compl_compl]; exact ih.1⟩

/-- In a local ring `R`, if `R ⧸ q` has dimension one, the only primes containing `q` are `q`
and the maximal ideal. -/
theorem eq_or_eq_maximalIdeal_of_ringKrullDim_quotient_eq_one {R : Type u} [CommRing R]
    [IsLocalRing R] (q : Ideal R) [q.IsPrime] (hq : ringKrullDim (R ⧸ q) = 1) (p : Ideal R)
    [p.IsPrime] (hqp : q ≤ p) : p = q ∨ p = maximalIdeal R := by
  classical
  have : Nontrivial (R ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
  have : IsLocalRing (R ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have h1 : (maximalIdeal (R ⧸ q)).height = 1 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R ⧸ q)
    rw [hq] at this
    exact_mod_cast this
  let pbar := p.map (Ideal.Quotient.mk q)
  have hpbar : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  have hcomap : pbar.comap (Ideal.Quotient.mk q) = p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hqp]
  by_cases hpm : pbar = maximalIdeal (R ⧸ q)
  · right
    have : (maximalIdeal (R ⧸ q)).comap (Ideal.Quotient.mk q) = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hcomap, hpm, this]
  · left
    have hlt : pbar < maximalIdeal (R ⧸ q) :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpbar.ne_top) hpm
    have h0 : pbar.height < (1 : ℕ) := (Ideal.height_le_iff (n := 1)).mp h1.le pbar hpbar hlt
    have h00 : pbar.height = 0 := by
      rw [Nat.cast_one] at h0
      exact Order.lt_one_iff.mp h0
    have hb : pbar = ⊥ := by
      rw [Ideal.height_eq_zero_iff] at h00
      exact le_bot_iff.mp (h00.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
    rw [← hcomap, hb, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- Given primes `𝔭 < 𝔪` of a noetherian ring and `s ∉ 𝔭`, there is a prime `𝔮` with
`𝔭 ≤ 𝔮 < 𝔪`, `s ∉ 𝔮`, and no prime strictly between `𝔮` and `𝔪`. -/
theorem exists_coheightOne {C : Type u} [CommRing C] [IsNoetherianRing C] (𝔭 𝔪 : Ideal C)
    [𝔭.IsPrime] [𝔪.IsPrime] (hpm : 𝔭 ≤ 𝔪) (hne : 𝔭 ≠ 𝔪) (s : C) (hs : s ∉ 𝔭) :
    ∃ 𝔮 : Ideal C, 𝔮.IsPrime ∧ 𝔭 ≤ 𝔮 ∧ 𝔮 ≤ 𝔪 ∧ 𝔮 ≠ 𝔪 ∧ s ∉ 𝔮 ∧
      ∀ p : Ideal C, p.IsPrime → 𝔮 ≤ p → p ≤ 𝔪 → p = 𝔮 ∨ p = 𝔪 := by
  classical
  let R₀ := Localization.AtPrime 𝔪
  have hdisj : ∀ {I : Ideal C}, I ≤ 𝔪 → Disjoint (𝔪.primeCompl : Set C) (I : Set C) := fun hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  let P : Ideal R₀ := 𝔭.map (algebraMap C R₀)
  have hP : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl R₀ 𝔭 ‹_› (hdisj hpm)
  have hPu : P.comap (algebraMap C R₀) = 𝔭 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl R₀ ‹_› (hdisj hpm)
  have hMu : (maximalIdeal R₀).comap (algebraMap C R₀) = 𝔪 := Localization.AtPrime.under_maximalIdeal
  have hMm : 𝔪.map (algebraMap C R₀) = maximalIdeal R₀ := Localization.AtPrime.map_eq_maximalIdeal
  have : Nontrivial (R₀ ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
  have : IsLocalRing (R₀ ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let φ : C →+* R₀ ⧸ P := (Ideal.Quotient.mk P).comp (algebraMap C R₀)
  have hφker : ∀ x, φ x = 0 ↔ x ∈ 𝔭 := fun x => by
    rw [← hPu, Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem
  have hnf : ¬ IsField (R₀ ⧸ P) := by
    intro hF
    have hPmax : P.IsMaximal := Ideal.Quotient.maximal_of_isField P hF
    apply hne
    rw [← hPu, IsLocalRing.eq_maximalIdeal hPmax, hMu]
  obtain ⟨qbar, hqbar, hsq, hdim⟩ :=
    IsLocalRing.exists_isPrime_not_mem_ringKrullDim_quotient_eq_one hnf (φ s)
      (fun h => hs ((hφker s).mp h))
  let Q : Ideal R₀ := qbar.comap (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : P ≤ Q := fun x hx => by
    show Ideal.Quotient.mk P x ∈ qbar
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact qbar.zero_mem
  have hQmap : Q.map (Ideal.Quotient.mk P) = qbar :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  refine ⟨Q.comap (algebraMap C R₀), Ideal.IsPrime.comap _, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPu.ge.trans (Ideal.comap_mono hPQ)
  · exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans hMu.le
  · intro hQm
    have hQM : Q = maximalIdeal R₀ := by
      have := IsLocalization.map_under 𝔪.primeCompl R₀ Q
      rw [Ideal.under, hQm, hMm] at this
      exact this.symm
    have hqM : qbar.IsMaximal := by
      rw [← hQmap, hQM]
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective (I := maximalIdeal R₀) inferInstance with htop | hmax
      · exact absurd (hQmap.symm.trans (hQM ▸ htop) ▸ hqbar.ne_top) (fun h => h rfl)
      · exact hmax
    have h0 : ringKrullDim ((R₀ ⧸ P) ⧸ qbar) = 0 := by
      let this := Ideal.Quotient.field qbar
      exact ringKrullDim_eq_zero_of_field _
    rw [h0] at hdim
    exact zero_ne_one hdim
  · rwa [Ideal.mem_comap, Ideal.mem_comap]
  · intro p hp hQp hpM
    have := hp
    let p₀ : Ideal R₀ := p.map (algebraMap C R₀)
    have hp₀ : p₀.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl R₀ p hp (hdisj hpM)
    have hp₀u : p₀.comap (algebraMap C R₀) = p :=
      IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl R₀ hp (hdisj hpM)
    have hQp₀ : Q ≤ p₀ := by
      have := IsLocalization.map_under 𝔪.primeCompl R₀ Q
      rw [← this]
      exact Ideal.map_mono hQp
    have : (p₀.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime (hPQ.trans hQp₀)
    have key := eq_or_eq_maximalIdeal_of_ringKrullDim_quotient_eq_one qbar hdim
      (p₀.map (Ideal.Quotient.mk P)) (by rw [← hQmap]; exact Ideal.map_mono hQp₀)
    have hback : (p₀.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = p₀ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr (hPQ.trans hQp₀)]
    rcases key with h | h
    · left
      rw [← hp₀u, ← hback, h]
    · right
      have : (maximalIdeal (R₀ ⧸ P)).comap (Ideal.Quotient.mk P) = maximalIdeal R₀ :=
        IsLocalRing.eq_maximalIdeal
          (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← hp₀u, ← hback, h, this, hMu]

section Mbar

variable {C : Type u} [CommRing C] (𝔮 𝔪 : Ideal C) [𝔮.IsPrime] [𝔪.IsPrime]

/-- The image of the ideal `𝔪` in `C ⧸ 𝔮`. -/
abbrev mbar : Ideal (C ⧸ 𝔮) := 𝔪.map (Ideal.Quotient.mk 𝔮)

omit [𝔮.IsPrime] [𝔪.IsPrime] in
theorem comap_mbar (hqm : 𝔮 ≤ 𝔪) : (mbar 𝔮 𝔪).comap (Ideal.Quotient.mk 𝔮) = 𝔪 := by
  rw [mbar, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hqm]

omit [𝔮.IsPrime] in
theorem mbar_isPrime (hqm : 𝔮 ≤ 𝔪) : (mbar 𝔮 𝔪).IsPrime :=
  Ideal.isPrime_map_quotientMk_of_isPrime hqm

omit [𝔮.IsPrime] [𝔪.IsPrime] in
theorem eq_bot_of_lt_mbar (hqm : 𝔮 ≤ 𝔪)
    (hcov : ∀ p : Ideal C, p.IsPrime → 𝔮 ≤ p → p ≤ 𝔪 → p = 𝔮 ∨ p = 𝔪)
    (P : Ideal (C ⧸ 𝔮)) [P.IsPrime] (hP : P < mbar 𝔮 𝔪) : P = ⊥ := by
  have h1 : 𝔮 ≤ P.comap (Ideal.Quotient.mk 𝔮) := fun c hc => by
    show Ideal.Quotient.mk 𝔮 c ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc]; exact P.zero_mem
  have h2 : P.comap (Ideal.Quotient.mk 𝔮) ≤ 𝔪 := by
    rw [← comap_mbar 𝔮 𝔪 hqm]; exact Ideal.comap_mono hP.le
  rcases hcov _ (Ideal.IsPrime.comap _) h1 h2 with h | h
  · have : P = (P.comap (Ideal.Quotient.mk 𝔮)).map (Ideal.Quotient.mk 𝔮) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
    rw [this, h, Ideal.map_quotient_self]
  · exfalso
    have : P = mbar 𝔮 𝔪 := by
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P, h]
    exact hP.ne this

theorem height_mbar (hqm : 𝔮 ≤ 𝔪) (hne : 𝔮 ≠ 𝔪)
    (hcov : ∀ p : Ideal C, p.IsPrime → 𝔮 ≤ p → p ≤ 𝔪 → p = 𝔮 ∨ p = 𝔪) :
    (mbar 𝔮 𝔪).height = 1 := by
  have := mbar_isPrime 𝔮 𝔪 hqm
  apply le_antisymm
  · refine (Ideal.height_le_iff (n := 1)).mpr fun P hP hPlt => ?_
    have := hP
    rw [eq_bot_of_lt_mbar 𝔮 𝔪 hqm hcov P hPlt, Ideal.height_bot]
    exact zero_lt_one
  · rw [Order.one_le_iff_ne_zero]
    intro h0
    rw [Ideal.height_eq_zero_iff] at h0
    have hb : mbar 𝔮 𝔪 = ⊥ := le_bot_iff.mp (h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
    apply hne
    rw [← comap_mbar 𝔮 𝔪 hqm, hb, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end Mbar

/-- A one-dimensional noetherian local domain `A` with fraction field `K` is dominated by a
discrete valuation ring of any finite extension `L` of `K`. -/
theorem exists_valuationSubring_dominates {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1)
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ a : A, algebraMap A L a ∈ V) ∧
      (∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A L a ∈ V.nonunits) := by
  classical
  have hA' : ¬ IsField A := fun hF => by
    have h0 : ringKrullDim A = 0 := by
      let this := hF.toField
      exact ringKrullDim_eq_zero_of_field A
    rw [h0] at hA; exact zero_ne_one hA
  obtain ⟨V₀, hV₀, hAV₀, hmV₀⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hA' K
  obtain ⟨V, hV, hV₀V, hmV₀V⟩ :=
    ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional (E := L) V₀ hV₀
  have hAV : ∀ a : A, algebraMap A L a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply A K L]; exact hV₀V _ (hAV₀ a)
  have hdom : ∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A L a ∈ V.nonunits := by
    intro a
    constructor
    · intro ha
      rw [IsScalarTower.algebraMap_apply A K L]
      have h1 : algebraMap A K a ∈ V₀.nonunits := (hmV₀ a).mp ha
      obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h1
      exact hmV₀V ⟨algebraMap A K a, hmem⟩ hmax
    · intro ha
      by_contra hna
      have hu : IsUnit a := by
        rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at hna
      obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp ha
      apply (mem_maximalIdeal _).mp hmax
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      refine ⟨⟨⟨algebraMap A L a, hmem⟩, ⟨algebraMap A L b, hAV b⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        show algebraMap A L a * algebraMap A L b = 1
        rw [← map_mul, hb, map_one]
      · apply Subtype.ext
        show algebraMap A L b * algebraMap A L a = 1
        rw [← map_mul, mul_comm, hb, map_one]
  exact ⟨V, hV, hAV, hdom⟩

/-- Let `g : X ⟶ Spec C` be locally of finite type over a noetherian ring, `x ∈ X`, and `t` a
point of `Spec C` that is a specialization of `g x` with no point strictly between them. Then
there is a valuative square of `g` with a discrete valuation ring whose closed point maps to `t`
and whose generic point maps into the closure of `x`. -/
theorem exists_valuativeCommSq_of_specializes {C : Type u} [CommRing C] [IsNoetherianRing C]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType g]
    (x : X) (t : ↥(Spec (CommRingCat.of C))) (hxt : g.base x ⤳ t) (hne : g.base x ≠ t)
    (hcov : ∀ p : Ideal C, p.IsPrime → (g.base x).asIdeal ≤ p → p ≤ t.asIdeal →
      p = (g.base x).asIdeal ∨ p = t.asIdeal) :
    ∃ S : ValuativeCommSq g, IsDiscreteValuationRing S.R ∧
      S.i₂.base (IsLocalRing.closedPoint S.R) = t ∧ Set.range S.i₁.base ⊆ closure {x} := by
  classical
  set 𝔮 : Ideal C := (g.base x).asIdeal with h𝔮def
  have hqm : 𝔮 ≤ t.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hxt
  have hneI : 𝔮 ≠ t.asIdeal := fun h => hne (PrimeSpectrum.ext h)
  have hmb : (mbar 𝔮 t.asIdeal).IsPrime := mbar_isPrime 𝔮 t.asIdeal hqm
  let R₀ : Type u := C ⧸ 𝔮
  let A : Type u := Localization.AtPrime (mbar 𝔮 t.asIdeal)
  let K₀ : Type u := FractionRing R₀
  have : IsDomain A :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := (mbar 𝔮 t.asIdeal).primeCompl) A
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing (mbar 𝔮 t.asIdeal).primeCompl A inferInstance
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (mbar 𝔮 t.asIdeal) A,
      height_mbar 𝔮 t.asIdeal hqm hneI hcov]
    rfl
  let iK : C →+* K₀ := (algebraMap R₀ K₀).comp (Ideal.Quotient.mk 𝔮)
  have hiK : RingHom.ker iK = 𝔮 := by
    rw [← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R₀ K₀),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let XK := pullback g (Spec.map (CommRingCat.ofHom iK))
  have : JacobsonSpace XK :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd g (Spec.map (CommRingCat.ofHom iK)))
  let pt : Spec (CommRingCat.of K₀) := IsLocalRing.closedPoint K₀
  have hpt : g.base x = (Spec.map (CommRingCat.ofHom iK)).base pt := by
    apply PrimeSpectrum.ext
    rw [Spec.map_apply]
    show 𝔮 = Ideal.comap iK (IsLocalRing.maximalIdeal K₀)
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField K₀),
      ← RingHom.ker_eq_comap_bot, hiK]
  obtain ⟨x', hx'1, -⟩ := Scheme.Pullback.exists_preimage_pullback x pt hpt
  obtain ⟨z', hz'cl, hz'c⟩ := nonempty_inter_closedPoints (Z := closure {x'})
    ⟨x', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hz'c
  have hxz : x ⤳ (pullback.fst g (Spec.map (CommRingCat.ofHom iK))).base z' := by
    rw [← hx'1]
    exact (specializes_iff_mem_closure.mpr hz'cl).map (pullback.fst g _).continuous
  let L : Type u := XK.residueField z'
  let ψ : CommRingCat.of K₀ ⟶ XK.residueField z' :=
    Spec.preimage (XK.fromSpecResidueField z' ≫ pullback.snd g (Spec.map (CommRingCat.ofHom iK)))
  have hψ : Spec.map ψ = XK.fromSpecResidueField z' ≫ pullback.snd g _ := Spec.map_preimage _
  have : IsClosedImmersion (XK.fromSpecResidueField z') :=
    isClosed_singleton_iff_isClosedImmersion.mp hz'c
  have hfinψ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace).mpr inferInstance
  let algKL : Algebra K₀ L := ψ.hom.toAlgebra
  have : Module.Finite K₀ L := hfinψ
  let algAL : Algebra A L := (ψ.hom.comp (algebraMap A K₀)).toAlgebra
  have : IsScalarTower A K₀ L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨V, hVdvr, hVsub, hVdom⟩ :=
    exists_valuationSubring_dominates (A := A) hdim (K := K₀) (L := L)
  let jV : A →+* ↥V := (algebraMap A L).codRestrict V hVsub
  let φC : C →+* ↥V := jV.comp ((algebraMap R₀ A).comp (Ideal.Quotient.mk 𝔮))
  have hcomm : ψ.hom.comp iK = (algebraMap (↥V) L).comp φC := by
    ext c
    show ψ.hom (algebraMap R₀ K₀ (Ideal.Quotient.mk 𝔮 c)) =
      algebraMap A L (algebraMap R₀ A (Ideal.Quotient.mk 𝔮 c))
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R₀ A K₀]
  have w : (XK.fromSpecResidueField z' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom iK))) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap (↥V) L)) ≫ Spec.map (CommRingCat.ofHom φC) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hψ, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 1
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact hcomm
  let Sq : ValuativeCommSq g :=
    ValuativeCommSq.mk (R := ↥V) (K := L)
      (XK.fromSpecResidueField z' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom iK)))
      (Spec.map (CommRingCat.ofHom φC)) ⟨w⟩
  refine ⟨Sq, hVdvr, ?_, ?_⟩
  · apply PrimeSpectrum.ext
    show ((Spec.map (CommRingCat.ofHom φC)).base (IsLocalRing.closedPoint ↥V)).asIdeal = t.asIdeal
    rw [Spec.map_apply]
    show Ideal.comap φC (IsLocalRing.maximalIdeal ↥V) = t.asIdeal
    have h1 : Ideal.comap jV (IsLocalRing.maximalIdeal ↥V) = IsLocalRing.maximalIdeal A := by
      ext a
      rw [Ideal.mem_comap, hVdom a, ← ValuationSubring.coe_mem_nonunits_iff]
      rfl
    rw [show Ideal.comap φC (IsLocalRing.maximalIdeal ↥V) =
        ((Ideal.comap jV (IsLocalRing.maximalIdeal ↥V)).comap (algebraMap R₀ A)).comap
          (Ideal.Quotient.mk 𝔮) by
      rw [Ideal.comap_comap, Ideal.comap_comap], h1]
    rw [← Ideal.under_def, Localization.AtPrime.under_maximalIdeal]
    exact comap_mbar 𝔮 t.asIdeal hqm
  · rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact specializes_iff_mem_closure.mp hxz

/-- Over a noetherian ring, the image of a closed subset `Z` under a morphism locally of finite
type with lifts for all valuative squares with a discrete valuation ring is stable under
specialization, provided the image is constructible. -/
theorem mem_image_of_specializes {C : Type u} [CommRing C] [IsNoetherianRing C]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType g]
    (H : ∀ S : ValuativeCommSq g, IsDiscreteValuationRing S.R → S.commSq.HasLift)
    (Z : Set X) (hZ : IsClosed Z) (hZc : IsConstructible (g.base '' Z))
    {t' t : ↥(Spec (CommRingCat.of C))} (ht' : t' ∈ g.base '' Z) (h : t' ⤳ t) :
    t ∈ g.base '' Z := by
  classical
  by_cases htt : t' = t
  · exact htt ▸ ht'
  obtain ⟨U, hU, ht'U, hUZ⟩ := exists_isOpen_inter_closure_subset hZc t' ht'
  obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hts, hsU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open ht'U hU
  have hle : t'.asIdeal ≤ t.asIdeal := (PrimeSpectrum.le_iff_specializes t' t).mpr h
  have hne : t'.asIdeal ≠ t.asIdeal := fun e => htt (PrimeSpectrum.ext e)
  obtain ⟨𝔮, h𝔮, hp𝔮, h𝔮m, h𝔮ne, hs𝔮, hcov⟩ :=
    exists_coheightOne t'.asIdeal t.asIdeal hle hne s hts
  let q : ↥(Spec (CommRingCat.of C)) := ⟨𝔮, h𝔮⟩
  have hqZ : q ∈ g.base '' Z := by
    refine hUZ ⟨hsU hs𝔮, ?_⟩
    exact (PrimeSpectrum.le_iff_mem_closure t' q).mp hp𝔮
  obtain ⟨z, hzZ, hz⟩ := hqZ
  have hzt : g.base z ⤳ t := by rw [hz]; exact (PrimeSpectrum.le_iff_specializes q t).mp h𝔮m
  have hznt : g.base z ≠ t := by
    rw [hz]; exact fun e => h𝔮ne (congrArg PrimeSpectrum.asIdeal e)
  obtain ⟨S, hR, hi₂, hi₁⟩ :=
    exists_valuativeCommSq_of_specializes g z t hzt hznt (by rw [hz]; exact hcov)
  obtain ⟨l, hl₁, hl₂⟩ := (H S hR).exists_lift
  refine ⟨l.base (closedPoint S.R), ?_, ?_⟩
  · have hgen : l.base ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base
        (closedPoint S.K)) ∈ closure {z} := by
      apply hi₁
      refine ⟨closedPoint S.K, ?_⟩
      rw [← hl₁]
      exact Scheme.Hom.comp_apply _ _ _
    have hsp : (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base (closedPoint S.K) ⤳
        closedPoint S.R :=
      IsLocalRing.specializes_closedPoint _
    have h1 := (hsp.map l.continuous).mem_closure
    have h2 : closure {l.base ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))).base
        (closedPoint S.K))} ⊆ closure {z} :=
      isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgen)
    have h3 : closure {z} ⊆ Z := hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzZ)
    exact h3 (h2 h1)
  · rw [← Scheme.Hom.comp_apply, hl₂, hi₂]

end NoetherianValuativeCriterion

open NoetherianValuativeCriterion in
/-- **Valuative criterion with discrete valuation rings.** Let `R` be a noetherian ring and
`f : X ⟶ Spec R` quasi-compact and locally of finite type. If every valuative square of `f` whose
valuation ring is a discrete valuation ring has a lift, then `f` is universally closed. -/
theorem universallyClosed_of_forall_isDiscreteValuationRing_hasLift {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    [LocallyOfFiniteType f]
    (H : ∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R → S.commSq.HasLift) :
    UniversallyClosed f := by
  classical
  apply AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial f
  intro ι _
  have HC : ∀ S : ValuativeCommSq
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))),
      IsDiscreteValuationRing S.R → S.commSq.HasLift := fun S hS =>
    hasLift_baseChange
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R)))))
      H S hS
  intro Z hZ
  have : IsLocallyNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R)))))
  have : CompactSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R)))))
  have : IsNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))) := {}
  have hZc : Topology.IsConstructible Z :=
    Topology.IsConstructible.of_compl
      ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl)
  have := locallyOfFinitePresentation_of_isNoetherianRing
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R)))))
  have himg := Scheme.Hom.isConstructible_image
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))) hZc
  refine PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible ?_ himg
  intro t' t hst ht'
  exact mem_image_of_specializes _ HC Z hZ himg ht' hst

end Langlands.AlgebraicGeometry
