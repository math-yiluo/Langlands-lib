import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusLevel
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalReduction

/-! # Standard local data, coverings by levels, and existence of levels

For a point `w` of `Spec (R'/𝔍)` with prime `P_w` of `R'` and local ring `O_w = R'_{P_w}`,
the quotients `O_w/𝔟` with `𝔍 O_w ≤ 𝔟 ≤ (𝔍 + 𝔞) O_w` are local data at `w` for every level
`ρ : R' → D` that is an epimorphism and kills `𝔞` (`stdDatum`). The lifting condition at `w`
only involves ring maps `β : R' → A` with `β⁻¹(𝔪_A) = P_w`; such maps factor through the
localizations `R'_P` with `P_w ≤ P` and through the quotients `R'/I^(n+1)` with `I ≤ P_w` and
`n` large (`killAt_of_localization`, `killAt_of_quotient`). Finally the hypotheses of
`ClosedEtaleLocusOpenStatement` give levels for these rings (`nonempty_level_localization`,
`nonempty_level_quotient`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'}

variable (𝔍) in
/-- The prime of `R'` below a point `w` of `Spec (R'/𝔍)`. -/
abbrev primeOf (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : Ideal R' :=
  w.asIdeal.comap (Ideal.Quotient.mk 𝔍)

instance (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : (primeOf 𝔍 w).IsPrime :=
  have := w.isPrime
  Ideal.IsPrime.comap _

variable (𝔍) in
/-- The local ring `O_w = R'_{P_w}`. -/
abbrev Ow (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : Type u :=
  Localization.AtPrime (primeOf 𝔍 w)

lemma le_primeOf (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : 𝔍 ≤ primeOf 𝔍 w := fun j hj => by
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hj]
  exact w.asIdeal.zero_mem

section Std

variable {D : Type u} [CommRing D] {ρ : R' →+* D} {w : Spec (CommRingCat.of (R' ⧸ 𝔍))}

lemma std_ne_top {𝔞 : Ideal R'} (h𝔞w : 𝔞 ≤ primeOf 𝔍 w) {𝔟 : Ideal (Ow 𝔍 w)}
    (h𝔟₂ : 𝔟 ≤ (𝔍 ⊔ 𝔞).map (algebraMap R' (Ow 𝔍 w))) : 𝔟 ≠ ⊤ := by
  have h : 𝔟 ≤ maximalIdeal (Ow 𝔍 w) := by
    refine h𝔟₂.trans ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (sup_le (le_primeOf w) h𝔞w)
  exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top h

lemma isLocalRing_std {𝔞 : Ideal R'} (h𝔞w : 𝔞 ≤ primeOf 𝔍 w) {𝔟 : Ideal (Ow 𝔍 w)}
    (h𝔟₂ : 𝔟 ≤ (𝔍 ⊔ 𝔞).map (algebraMap R' (Ow 𝔍 w))) : IsLocalRing (Ow 𝔍 w ⧸ 𝔟) :=
  have : Nontrivial (Ow 𝔍 w ⧸ 𝔟) := Ideal.Quotient.nontrivial_iff.2 (std_ne_top h𝔞w h𝔟₂)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔟) Ideal.Quotient.mk_surjective

/-- The standard local datum `O_w/𝔟` at `w` for an epimorphic level `ρ` killing `𝔞`. -/
def stdDatum
    (hρ : ∀ (C : Type u) [CommRing C] (δ₁ δ₂ : D →+* C), δ₁.comp ρ = δ₂.comp ρ → δ₁ = δ₂)
    (𝔞 : Ideal R') (h𝔞ρ : 𝔞 ≤ RingHom.ker ρ)
    (𝔟 : Ideal (Ow 𝔍 w)) [IsLocalRing (Ow 𝔍 w ⧸ 𝔟)]
    (h𝔟₁ : 𝔍.map (algebraMap R' (Ow 𝔍 w)) ≤ 𝔟)
    (h𝔟₂ : 𝔟 ≤ (𝔍 ⊔ 𝔞).map (algebraMap R' (Ow 𝔍 w)))
    (δL : D →+* Ow 𝔍 w ⧸ 𝔟) (hδ : δL.comp ρ = (Ideal.Quotient.mk 𝔟).comp (algebraMap R' _))
    (f : Spec (CommRingCat.of (Ow 𝔍 w ⧸ 𝔟)) ⟶ Spec R)
    (hf : Spec.map (CommRingCat.ofHom (((Ideal.quotientMap 𝔟 (algebraMap R' (Ow 𝔍 w))
      (Ideal.map_le_iff_le_comap.1 h𝔟₁)).comp (Ideal.Quotient.mk 𝔍)).comp
        (algebraMap R R'))) = f) :
    LocalDatum R 𝔍 ρ w (Ow 𝔍 w ⧸ 𝔟) :=
  have hmk : (maximalIdeal (Ow 𝔍 w ⧸ 𝔟)).comap (Ideal.Quotient.mk 𝔟) = maximalIdeal (Ow 𝔍 w) :=
    have := IsLocalHom.of_surjective (Ideal.Quotient.mk 𝔟) Ideal.Quotient.mk_surjective
    congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk 𝔟))
  { ℓ := Ideal.quotientMap 𝔟 (algebraMap R' (Ow 𝔍 w)) (Ideal.map_le_iff_le_comap.1 h𝔟₁)
    δ := δL
    f := f
    hf := hf
    comm := by
      rw [Ideal.quotientMap_comp_mk, hδ]
    comap_eq := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk 𝔍) Ideal.Quotient.mk_surjective
      rw [Ideal.comap_comap, Ideal.quotientMap_comp_mk, ← Ideal.comap_comap, hmk]
      exact Localization.AtPrime.under_maximalIdeal
    univ := by
      intro C _ _ γ δ' hγ hcomap
      have hunit : ∀ s : (primeOf 𝔍 w).primeCompl,
          IsUnit ((γ.comp (Ideal.Quotient.mk 𝔍)) s) := by
        intro s
        by_contra hs
        apply s.2
        show Ideal.Quotient.mk 𝔍 (s : R') ∈ w.asIdeal
        rw [← hcomap, Ideal.mem_comap]
        exact (IsLocalRing.mem_maximalIdeal _).2 hs
      let β' : Ow 𝔍 w →+* C :=
        IsLocalization.lift (M := (primeOf 𝔍 w).primeCompl) (S := Ow 𝔍 w) hunit
      have hβ' : β'.comp (algebraMap R' (Ow 𝔍 w)) = γ.comp (Ideal.Quotient.mk 𝔍) :=
        IsLocalization.lift_comp hunit
      have hβ'r : ∀ r, β' (algebraMap R' (Ow 𝔍 w) r) = γ (Ideal.Quotient.mk 𝔍 r) :=
        fun r => RingHom.congr_fun hβ' r
      have hkill : ∀ x ∈ 𝔟, β' x = 0 := by
        intro x hx
        have h1 : 𝔟 ≤ RingHom.ker β' := by
          refine h𝔟₂.trans ?_
          rw [Ideal.map_le_iff_le_comap]
          refine sup_le (fun j hj => ?_) (fun a ha => ?_)
          · rw [Ideal.mem_comap, RingHom.mem_ker, hβ'r, Ideal.Quotient.eq_zero_iff_mem.2 hj,
              map_zero]
          · rw [Ideal.mem_comap, RingHom.mem_ker, hβ'r]
            have := RingHom.congr_fun hγ a
            simp only [RingHom.comp_apply] at this
            rw [this, RingHom.mem_ker.1 (h𝔞ρ ha), map_zero]
        exact h1 hx
      let μ : Ow 𝔍 w ⧸ 𝔟 →+* C := Ideal.Quotient.lift 𝔟 β' hkill
      have hμℓ : μ.comp (Ideal.quotientMap 𝔟 (algebraMap R' (Ow 𝔍 w))
          (Ideal.map_le_iff_le_comap.1 h𝔟₁)) = γ := by
        apply Ideal.Quotient.ringHom_ext
        ext r
        exact hβ'r r
      refine ⟨μ, ?_, hμℓ, ?_⟩
      · constructor
        intro l hl
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective l
        obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (primeOf 𝔍 w).primeCompl x
        have h1 : IsUnit (β' (IsLocalization.mk' (Ow 𝔍 w) r s)) := hl
        have h2 : β' (algebraMap R' _ r) =
            β' (IsLocalization.mk' (Ow 𝔍 w) r s) * β' (algebraMap R' _ s) := by
          rw [← map_mul, IsLocalization.mk'_spec]
        have h3 : IsUnit (γ (Ideal.Quotient.mk 𝔍 r)) := by
          rw [← hβ'r, h2]
          exact h1.mul ((IsLocalization.map_units (Ow 𝔍 w) s).map β')
        have h4 : r ∈ (primeOf 𝔍 w).primeCompl := fun hr => by
          have : Ideal.Quotient.mk 𝔍 r ∈ w.asIdeal := hr
          rw [← hcomap, Ideal.mem_comap] at this
          exact (IsLocalRing.mem_maximalIdeal _).1 this h3
        exact ((IsLocalization.AtPrime.isUnit_mk'_iff (Ow 𝔍 w) (primeOf 𝔍 w) r s).2 h4).map _
      · apply hρ
        rw [RingHom.comp_assoc, hδ, ← hγ]
        ext r
        exact hβ'r r
    gen := by
      intro l
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective l
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (primeOf 𝔍 w).primeCompl x
      have hs : δL (ρ s) = Ideal.Quotient.mk 𝔟 (algebraMap R' _ s) := RingHom.congr_fun hδ s
      have hr : δL (ρ r) = Ideal.Quotient.mk 𝔟 (algebraMap R' _ r) := RingHom.congr_fun hδ r
      refine ⟨ρ r, ρ s, ?_, ?_⟩
      · rw [hs]
        exact (IsLocalization.map_units (Ow 𝔍 w) s).map _
      · rw [hs, hr, ← map_mul, IsLocalization.mk'_spec] }

end Std

section Cover

variable (ξ : F.obj (op (chart R R' 𝔍))) (w : Spec (CommRingCat.of (R' ⧸ 𝔍)))

/-- The lifting condition at `w` only involves maps `β` with `β⁻¹(𝔪_A) = P_w`. -/
lemma killAt_of_comap {A : Type u} [CommRing A] [IsLocalRing A] (β : R' →+* A)
    (H : (maximalIdeal A).comap β = primeOf 𝔍 w → KillAt ξ w A β) : KillAt ξ w A β := by
  intro f hf J hJ u₀ hc hw v hv
  refine H ?_ f hf J hJ u₀ hc hw v hv
  have := Charts.isLocalRing_quotient hJ
  obtain ⟨γ₀, hγ₀⟩ := exists_specMap_ofHom u₀.left
  have h1 : (Ideal.Quotient.mk J).comp β = γ₀.comp (Ideal.Quotient.mk 𝔍) := by
    rw [← specMap_ofHom_inj, ← hc, ← hγ₀, specMap_ofHom_comp]
  have h2 : (maximalIdeal (A ⧸ J)).comap γ₀ = w.asIdeal := by
    have := hw (closedPoint _)
    rw [← hγ₀] at this
    exact congrArg PrimeSpectrum.asIdeal this
  have h3 : (maximalIdeal (A ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal A := by
    have := IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    exact congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk J))
  rw [← h3, Ideal.comap_comap, h1, ← Ideal.comap_comap, h2]

/-- Maps `β` with `β⁻¹(𝔪_A) = P_w` factor through `R'_P` for `P_w ≤ P`. -/
lemma killAt_of_localization (P : Ideal R') [P.IsPrime] (hP : primeOf 𝔍 w ≤ P) {A : Type u}
    [CommRing A] [IsLocalRing A] (β : R' →+* A)
    (H : ∀ δ' : Localization.AtPrime P →+* A, KillAt ξ w A (δ'.comp (algebraMap R' _))) :
    KillAt ξ w A β := by
  apply killAt_of_comap ξ w β
  intro hβ
  have hunit : ∀ s : P.primeCompl, IsUnit (β s) := by
    intro s
    by_contra hs
    apply s.2
    apply hP
    rw [← hβ, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).2 hs
  have := H (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit)
  rwa [IsLocalization.lift_comp] at this

/-- Maps `β` with `β⁻¹(𝔪_A) = P_w` to a local artinian ring factor through `R'/I^(n+1)` for
`I ≤ P_w` and all large `n`. -/
lemma killAt_of_quotient (I : Ideal R') (hI : I ≤ primeOf 𝔍 w) {A : Type u} [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] (β : R' →+* A) (n₀ : ℕ)
    (H : ∀ n ≥ n₀, ∀ δ' : R' ⧸ I ^ (n + 1) →+* A,
      KillAt ξ w A (δ'.comp (Ideal.Quotient.mk _))) :
    KillAt ξ w A β := by
  apply killAt_of_comap ξ w β
  intro hβ
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 inferInstance
  have hIβ : I.map β ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap, hβ]
    exact hI
  have hker : I ^ (max n₀ N + 1) ≤ RingHom.ker β := by
    rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff]
    calc I.map β ^ (max n₀ N + 1) ≤ maximalIdeal A ^ (max n₀ N + 1) :=
          Ideal.pow_right_mono hIβ _
      _ ≤ maximalIdeal A ^ N := Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := hN.trans Ideal.zero_eq_bot
  have := H (max n₀ N) (le_max_left _ _) (Ideal.Quotient.lift _ β (fun a ha => hker ha))
  have e : (Ideal.Quotient.lift (I ^ (max n₀ N + 1)) β (fun a ha => hker ha)).comp
      (Ideal.Quotient.mk _) = β := RingHom.ext fun _ => rfl
  rw [e] at this
  exact this

end Cover

section Existence

variable (F)

/-- The hypothesis on local schemes gives levels `R' → R'_P`. -/
lemma nonempty_level_localization
    (hloc : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    (P : Ideal R') [P.IsPrime] :
    Nonempty (Level F (algebraMap R' (Localization.AtPrime P))) := by
  let s : Spec R := ⟨P.comap (algebraMap R R'), inferInstance⟩
  have hs0 : levelMap R (algebraMap R' (Localization.AtPrime P))
      (closedPoint (CommRingCat.of (Localization.AtPrime P))) = s := by
    apply PrimeSpectrum.ext
    change (maximalIdeal _).comap ((algebraMap R' (Localization.AtPrime P)).comp
      (algebraMap R R')) = P.comap (algebraMap R R')
    rw [← Ideal.comap_comap]
    congr 1
    exact Localization.AtPrime.under_maximalIdeal
  obtain ⟨f', hf'⟩ := Charts.exists_comp_fromSpecStalk s
    (levelMap R (algebraMap R' (Localization.AtPrime P))) (by rw [hs0])
  have h := LocalToGlobal.unramifiedRepresentable_of_iso
    (LocalToGlobal.baseChangeCompIso f' _ F)
    (LocalToGlobal.unramifiedRepresentable_baseChange (hloc s) f')
  rw [hf'] at h
  obtain ⟨Y, q, ⟨e⟩, -, h₂, h₃⟩ := h
  exact ⟨{ X := Y, q := q, e := e, lft := h₂, fu := h₃ }⟩

/-- The hypothesis on closed subschemes gives levels `R' → R'/J` for `J = I R'` with `I ≠ 0`. -/
lemma nonempty_level_quotient
    (hquot : ∀ I : Ideal R, I ≠ ⊥ → UnramifiedRepresentable
      (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F))
    (I : Ideal R) (hI : I ≠ ⊥) (J : Ideal R') (hJ : I.map (algebraMap R R') = J) :
    Nonempty (Level F (Ideal.Quotient.mk J)) := by
  subst hJ
  let g : Spec (CommRingCat.of (R' ⧸ I.map (algebraMap R R'))) ⟶
      Spec (CommRingCat.of (R ⧸ I)) :=
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap R R') Ideal.le_comap_map))
  have hg : (g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :
      Spec (CommRingCat.of (R' ⧸ I.map (algebraMap R R'))) ⟶ Spec R) =
      levelMap R (Ideal.Quotient.mk (I.map (algebraMap R R'))) := by
    rw [specMap_ofHom_comp, levelMap, Ideal.quotientMap_comp_mk]
  have h := LocalToGlobal.unramifiedRepresentable_of_iso
    (LocalToGlobal.baseChangeCompIso g _ F)
    (LocalToGlobal.unramifiedRepresentable_baseChange (hquot I hI) g)
  rw [hg] at h
  obtain ⟨Y, q, ⟨e⟩, -, h₂, h₃⟩ := h
  exact ⟨{ X := Y, q := q, e := e, lft := h₂, fu := h₃ }⟩

end Existence

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
