import Langlands.CommutativeAlgebra.NearIdentityQuotientComparison
import Langlands.CommutativeAlgebra.SquareSurjectivePowers
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Rigidity of quotients by approximate generators

Let `σ : S → Q` be a map from a polynomial ring to a ring `Q` that is surjective modulo
every power of an ideal `𝔫` with `σ⁻¹(𝔫 ^ n) = 𝔪 ^ n`, and let `π : Q → A` be surjective.
Let `T₀` be an `S`-algebra mapping to `Q`, unramified at `u₀ = ι₀⁻¹(𝔫)` in the sense
that `T₀ = S + u₀ ^ 2`, and let `b'` be elements of `T₀` whose images satisfy the
Artin–Rees comparison with `ker π`. Then every algebra map `A → T / m_T ^ n`
(`T = T₀ / (b')`) that is local and reduces on `S` to the canonical map modulo
`m_T ^ 2` is surjective with kernel `m_A ^ n`. -/

universe u v w₁ w₂ w₃

open Ideal

namespace Langlands.CommutativeAlgebra.ApproximateQuotientRigidity

variable {R : Type u} [CommRing R] {ι : Type v}
  {Q : Type w₂} [CommRing Q]
  (𝔪 : Ideal (MvPolynomial ι R)) (𝔫 : Ideal Q) (σ : MvPolynomial ι R →+* Q)

section Approximation

variable (hσ1 : ∀ n (x : Q), ∃ s, x - σ s ∈ 𝔫 ^ n) (hσ3 : 𝔫 = 𝔪.map σ)
include hσ1 hσ3

/-- Elements of `𝔫 ^ k` are approximated by images of `𝔪 ^ k` modulo every `𝔫 ^ n`. -/
theorem exists_mem_pow_sub_mem (k n : ℕ) (f : Q) (hf : f ∈ 𝔫 ^ k) :
    ∃ s ∈ 𝔪 ^ k, f - σ s ∈ 𝔫 ^ n := by
  rw [hσ3, ← Ideal.map_pow] at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp⟩
  · exact ⟨0, Ideal.zero_mem _, by simp⟩
  · rintro x y - - ⟨s₁, hs₁, e₁⟩ ⟨s₂, hs₂, e₂⟩
    refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
    have : x + y - σ (s₁ + s₂) = (x - σ s₁) + (y - σ s₂) := by rw [map_add]; ring
    rw [this]; exact Ideal.add_mem _ e₁ e₂
  · rintro a x - ⟨s₂, hs₂, e₂⟩
    obtain ⟨s₁, e₁⟩ := hσ1 n a
    refine ⟨s₁ * s₂, Ideal.mul_mem_left _ _ hs₂, ?_⟩
    have : a • x - σ (s₁ * s₂) = σ s₁ * (x - σ s₂) + (a - σ s₁) * x := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ e₂) (Ideal.mul_mem_right _ _ e₁)

end Approximation

section Model

variable {T₀ : Type w₃} [CommRing T₀] [Algebra R T₀]
  (σT : MvPolynomial ι R →ₐ[R] T₀) (ι₀ : T₀ →+* Q)

/-- The ideal of `T₀` over `𝔫`. -/
abbrev u₀ : Ideal T₀ := 𝔫.comap ι₀

variable (hσ2 : ∀ n s, σ s ∈ 𝔫 ^ n → s ∈ 𝔪 ^ n) (hσ3 : 𝔫 = 𝔪.map σ)
  (hισ : ∀ s, ι₀ (σT s) = σ s) (hT : ∀ t, ∃ s, t - σT s ∈ u₀ 𝔫 ι₀ ^ 2)

include hσ3 hισ in
lemma σT_mem_pow {n : ℕ} {s : MvPolynomial ι R} (hs : s ∈ 𝔪 ^ n) :
    σT s ∈ u₀ 𝔫 ι₀ ^ n := by
  have h𝔪 : 𝔪.map σT.toRingHom ≤ u₀ 𝔫 ι₀ := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    change ι₀ (σT m) ∈ 𝔫
    rw [hισ, hσ3]
    exact Ideal.mem_map_of_mem _ hm
  have : σT s ∈ (𝔪.map σT.toRingHom) ^ n := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem σT.toRingHom hs
  exact Ideal.pow_right_mono h𝔪 n this

include hσ2 hσ3 hισ hT in
/-- The preimage of `𝔫 ^ k` in `T₀` is `u₀ ^ k`. -/
theorem mem_u₀_pow_of_mem {k : ℕ} {t : T₀} (ht : ι₀ t ∈ 𝔫 ^ k) : t ∈ u₀ 𝔫 ι₀ ^ k := by
  obtain ⟨s, hs⟩ := SquareSurjectivePowers.exists_sub_mem_pow σT.toRingHom (u₀ 𝔫 ι₀) hT k t
  have hv : ι₀ (t - σT s) ∈ 𝔫 ^ k := by
    have := SquareSurjectivePowers.map_mem_pow ι₀ (𝔫) (show t - σT s ∈ (𝔫.comap ι₀) ^ k from hs)
    exact this
  have hσs : σ s ∈ 𝔫 ^ k := by
    rw [← hισ]
    have : ι₀ (σT s) = ι₀ t - ι₀ (t - σT s) := by rw [map_sub]; ring
    rw [this]; exact Ideal.sub_mem _ ht hv
  have : t = (t - σT s) + σT s := by ring
  rw [this]
  exact Ideal.add_mem _ hs (σT_mem_pow 𝔪 𝔫 σ σT ι₀ hσ3 hισ (hσ2 k s hσs))

variable {r : ℕ} (b' : Fin r → T₀)

/-- The maximal ideal of the quotient `T = T₀ / (b')`. -/
abbrev mT : Ideal (T₀ ⧸ Ideal.span (Set.range b')) :=
  (u₀ 𝔫 ι₀).map (Ideal.Quotient.mk _)

/-- The canonical map from `S` to the truncations of `T`. -/
noncomputable abbrev q (n : ℕ) :
    MvPolynomial ι R →ₐ[R] (T₀ ⧸ Ideal.span (Set.range b')) ⧸ mT 𝔫 ι₀ b' ^ n :=
  (Ideal.Quotient.mkₐ R _).comp ((Ideal.Quotient.mkₐ R _).comp σT)

lemma mk_mem_mT_pow_iff (n : ℕ) (t : T₀) :
    Ideal.Quotient.mk (Ideal.span (Set.range b')) t ∈ mT 𝔫 ι₀ b' ^ n ↔
      t ∈ u₀ 𝔫 ι₀ ^ n ⊔ Ideal.span (Set.range b') := by
  rw [mT, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]

include hT in
/-- The canonical map from `S` to each truncation of `T` is surjective. -/
theorem q_surjective (n : ℕ) : Function.Surjective (q 𝔫 σT ι₀ b' n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, hs⟩ := SquareSurjectivePowers.exists_sub_mem_pow σT.toRingHom (u₀ 𝔫 ι₀) hT n t
  refine ⟨s, ?_⟩
  change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (σT s)) = _
  rw [Ideal.Quotient.eq, ← map_sub, mk_mem_mT_pow_iff]
  have : σT s - t = -(t - σT s) := by ring
  rw [this]
  exact Ideal.mem_sup_left (neg_mem hs)

variable (hσ1 : ∀ n (x : Q), ∃ s, x - σ s ∈ 𝔫 ^ n)

include hσ1 hσ2 hσ3 hισ hT in
/-- The kernel of the canonical map to the `n`-th truncation of `T`. -/
theorem q_eq_zero_iff (n : ℕ) (s : MvPolynomial ι R) :
    q 𝔫 σT ι₀ b' n s = 0 ↔
      σ s ∈ Ideal.span (Set.range (fun j => ι₀ (b' j))) ⊔ 𝔫 ^ n := by
  change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (σT s)) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mk_mem_mT_pow_iff]
  constructor
  · intro h
    obtain ⟨v, hv, c, hc, hvc⟩ := Submodule.mem_sup.mp h
    rw [← hισ, ← hvc, map_add]
    refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left ?_)
    · exact SquareSurjectivePowers.map_mem_pow ι₀ 𝔫 hv
    · have : Ideal.map ι₀ (Ideal.span (Set.range b')) ≤
          Ideal.span (Set.range (fun j => ι₀ (b' j))) := by
        rw [Ideal.map_span, ← Set.range_comp]; rfl
      exact this (Ideal.mem_map_of_mem ι₀ hc)
  · intro h
    obtain ⟨j', hj', e, he, hje⟩ := Submodule.mem_sup.mp h
    obtain ⟨p, hp⟩ := Ideal.mem_span_range_iff_exists_fun.mp hj'
    choose sp hsp using fun j => hσ1 n (p j)
    -- `t := σT s - Σ σT (sp j) * b' j` maps into `𝔫 ^ n`
    have ht : ι₀ (σT s - ∑ j, σT (sp j) * b' j) ∈ 𝔫 ^ n := by
      have : ι₀ (σT s - ∑ j, σT (sp j) * b' j) =
          ∑ j, (p j - σ (sp j)) * ι₀ (b' j) + e := by
        rw [map_sub, map_sum, hισ, ← hje, ← hp]
        simp only [map_mul, hισ, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [this]
      exact Ideal.add_mem _ (Submodule.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hsp j)) he
    have := mem_u₀_pow_of_mem 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT ht
    have hsum : ∑ j, σT (sp j) * b' j ∈ Ideal.span (Set.range b') :=
      Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : σT s = (σT s - ∑ j, σT (sp j) * b' j) + ∑ j, σT (sp j) * b' j := by ring
    rw [this]
    exact Submodule.add_mem_sup ‹_› hsum

end Model

section Rigidity

variable {A : Type w₁} [CommRing A] [Algebra R A] {T₀ : Type w₃} [CommRing T₀] [Algebra R T₀]
  (σT : MvPolynomial ι R →ₐ[R] T₀) (ι₀ : T₀ →+* Q)
  (σA : MvPolynomial ι R →ₐ[R] A) (π : Q →+* A) (mA : Ideal A)
  (hπσ : ∀ s, π (σ s) = σA s)
  (hπ : ∀ n, (mA ^ n).comap π = RingHom.ker π ⊔ 𝔫 ^ n) (hπs : Function.Surjective π)
  (hσ1 : ∀ n (x : Q), ∃ s, x - σ s ∈ 𝔫 ^ n)
  (hσ2 : ∀ n s, σ s ∈ 𝔫 ^ n → s ∈ 𝔪 ^ n) (hσ3 : 𝔫 = 𝔪.map σ)
  (hισ : ∀ s, ι₀ (σT s) = σ s) (hT : ∀ t, ∃ s, t - σT s ∈ u₀ 𝔫 ι₀ ^ 2)

include hπσ hπ in
lemma σA_mem_pow_iff (n : ℕ) (s : MvPolynomial ι R) :
    σA s ∈ mA ^ n ↔ σ s ∈ RingHom.ker π ⊔ 𝔫 ^ n := by
  rw [← hπσ, ← Ideal.mem_comap, hπ]

include hπσ hπ hπs hσ1 in
/-- The map from `S` to the truncations of `A` is surjective. -/
lemma exists_sub_σA_mem_pow (n : ℕ) (a : A) : ∃ s, a - σA s ∈ mA ^ n := by
  obtain ⟨x, rfl⟩ := hπs a
  obtain ⟨s, hs⟩ := hσ1 n x
  refine ⟨s, ?_⟩
  rw [← hπσ, ← map_sub, ← Ideal.mem_comap, hπ]
  exact Ideal.mem_sup_right hs

variable {r : ℕ} (b' : Fin r → T₀)
  (hAR : ∀ d, ∀ z ∈ Ideal.span (Set.range (fun j => ι₀ (b' j))), z ∈ 𝔫 ^ d →
    z ∈ RingHom.ker π ⊔ 𝔫 ^ (d + 1))

include hπσ hπ hπs hσ1 hσ2 hσ3 hισ hT hAR in
/-- **Rigidity.** A local algebra map `A → T / m_T ^ n` reducing on `S` to the canonical
map modulo `m_T ^ 2` is surjective with kernel `m_A ^ n`. -/
theorem rigidity {n : ℕ} (hn : 2 ≤ n)
    (φ : A →ₐ[R] (T₀ ⧸ Ideal.span (Set.range b')) ⧸ mT 𝔫 ι₀ b' ^ n)
    (hloc : ∀ a ∈ mA, φ a ∈ (mT 𝔫 ι₀ b').map (Ideal.Quotient.mk _))
    (hred : ∀ s, Ideal.Quotient.factor (Ideal.pow_le_pow_right hn) (φ (σA s)) =
      q 𝔫 σT ι₀ b' 2 s) :
    Function.Surjective φ ∧ RingHom.ker φ = mA ^ n := by
  classical
  -- `φ` kills `m_A ^ n`
  have hkill : ∀ a ∈ mA ^ n, φ a = 0 := by
    intro a ha
    have h1 : mA.map φ.toRingHom ≤ (mT 𝔫 ι₀ b').map (Ideal.Quotient.mk _) := by
      rw [Ideal.map_le_iff_le_comap]; exact hloc
    have h2 : φ a ∈ ((mT 𝔫 ι₀ b').map (Ideal.Quotient.mk _)) ^ n := by
      refine Ideal.pow_right_mono h1 n ?_
      have h3 : φ a ∈ (mA ^ n).map φ.toRingHom := Ideal.mem_map_of_mem φ.toRingHom ha
      rwa [Ideal.map_pow φ.toRingHom mA n] at h3
    have h4 : ((mT 𝔫 ι₀ b').map (Ideal.Quotient.mk (mT 𝔫 ι₀ b' ^ n))) ^ n = ⊥ := by
      rw [← Ideal.map_pow (Ideal.Quotient.mk (mT 𝔫 ι₀ b' ^ n)) (mT 𝔫 ι₀ b') n,
        Ideal.map_quotient_self]
    rwa [h4, Ideal.mem_bot] at h2
  -- corrections in `𝔪 ^ 2`
  have hcorr : ∀ x, Ideal.Quotient.factor (Ideal.pow_le_pow_right hn) x = 0 →
      ∃ d ∈ 𝔪 ^ 2, q 𝔫 σT ι₀ b' n d = x := by
    intro x hx
    obtain ⟨s, rfl⟩ := q_surjective 𝔫 σT ι₀ hT b' n x
    have h2 : q 𝔫 σT ι₀ b' 2 s = 0 := by
      rw [← hx]; rfl
    rw [q_eq_zero_iff 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT b' hσ1] at h2
    obtain ⟨j', hj', e, he, hje⟩ := Submodule.mem_sup.mp h2
    obtain ⟨d, hd, hde⟩ := exists_mem_pow_sub_mem 𝔪 𝔫 σ hσ1 hσ3 2 n e he
    refine ⟨d, hd, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub, q_eq_zero_iff 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT b' hσ1]
    have : σ (s - d) = j' + (e - σ d) := by rw [map_sub, ← hje]; ring
    rw [this]
    exact Submodule.add_mem_sup hj' hde
  have hdiff : ∀ i : ι, Ideal.Quotient.factor (Ideal.pow_le_pow_right hn)
      (φ (σA (MvPolynomial.X i)) - q 𝔫 σT ι₀ b' n (MvPolynomial.X i)) = 0 := by
    intro i
    rw [map_sub, hred, sub_eq_zero]
    rfl
  choose d hd hqd using fun i => hcorr _ (hdiff i)
  let Φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.aeval fun i => MvPolynomial.X i + d i
  have hΦq : (q 𝔫 σT ι₀ b' n).comp Φ = φ.comp σA := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [Φ, AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, hqd]
    ring
  have hΦ2 : ∀ x, Φ x - x ∈ 𝔪 ^ 2 := by
    have : (Ideal.Quotient.mkₐ R (𝔪 ^ 2)).comp Φ = Ideal.Quotient.mkₐ R (𝔪 ^ 2) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [Φ, AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk,
        map_add, add_eq_left]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hd i)
    intro x
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun this x
  have hΦ := NearIdentityQuotientComparison.sub_mem_pow_succ_of_forall_sub_mem_sq 𝔪
    Φ.toRingHom hΦ2
  -- the comparison ideals
  set I : Ideal (MvPolynomial ι R) := (mA ^ n).comap σA.toRingHom with hIdef
  set I' : Ideal (MvPolynomial ι R) := RingHom.ker (q 𝔫 σT ι₀ b' n).toRingHom with hI'def
  have h𝔪I : 𝔪 ^ n ≤ I := by
    intro s hs
    change σA s ∈ mA ^ n
    rw [σA_mem_pow_iff 𝔫 σ σA π mA hπσ hπ]
    refine Ideal.mem_sup_right ?_
    rw [hσ3, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hs
  have hI : ∀ x ∈ I, Φ.toRingHom x ∈ I' ⊔ 𝔪 ^ n := by
    intro x hx
    refine Ideal.mem_sup_left ?_
    rw [hI'def, RingHom.mem_ker]
    change (q 𝔫 σT ι₀ b' n).comp Φ x = 0
    rw [hΦq, AlgHom.comp_apply]
    exact hkill _ hx
  have hAR' : ∀ d < n, I' ⊓ 𝔪 ^ d ≤ I ⊔ 𝔪 ^ (d + 1) := by
    intro dd hdd s ⟨hs₁, hs₂⟩
    have hs₁' : q 𝔫 σT ι₀ b' n s = 0 := hs₁
    rw [q_eq_zero_iff 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT b' hσ1] at hs₁'
    obtain ⟨j', hj', e, he, hje⟩ := Submodule.mem_sup.mp hs₁'
    have hσs : σ s ∈ 𝔫 ^ dd := by
      rw [hσ3, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hs₂
    have hed : e ∈ 𝔫 ^ dd := Ideal.pow_le_pow_right hdd.le he
    have hj'd : j' ∈ 𝔫 ^ dd := by
      have : j' = σ s - e := by rw [← hje]; ring
      rw [this]; exact Ideal.sub_mem _ hσs hed
    obtain ⟨j, hj, f, hf, hjf⟩ := Submodule.mem_sup.mp (hAR dd j' hj' hj'd)
    have hfe : f + e ∈ 𝔫 ^ (dd + 1) :=
      Ideal.add_mem _ hf (Ideal.pow_le_pow_right (by omega) he)
    obtain ⟨sf, hsf, hsfe⟩ := exists_mem_pow_sub_mem 𝔪 𝔫 σ hσ1 hσ3 (dd + 1) n _ hfe
    have hmem : s - sf ∈ I := by
      change σA (s - sf) ∈ mA ^ n
      rw [σA_mem_pow_iff 𝔫 σ σA π mA hπσ hπ]
      have : σ (s - sf) = j + (f + e - σ sf) := by rw [map_sub, ← hje, ← hjf]; ring
      rw [this]
      exact Submodule.add_mem_sup hj hsfe
    have : s = (s - sf) + sf := by ring
    rw [this]
    exact Submodule.add_mem_sup hmem hsf
  have hq' : RingHom.ker (q 𝔫 σT ι₀ b' n).toRingHom = I' ⊔ 𝔪 ^ n := by
    rw [hI'def, left_eq_sup]
    intro s hs
    rw [RingHom.mem_ker]
    change q 𝔫 σT ι₀ b' n s = 0
    rw [q_eq_zero_iff 𝔪 𝔫 σ σT ι₀ hσ2 hσ3 hισ hT b' hσ1]
    refine Ideal.mem_sup_right ?_
    rw [hσ3, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hs
  obtain ⟨hker, hsurj⟩ := NearIdentityQuotientComparison.ker_comp_eq_and_surjective hΦ hI hAR'
    (q 𝔫 σT ι₀ b' n).toRingHom hq' (q_surjective 𝔫 σT ι₀ hT b' n)
  have hcomp : (q 𝔫 σT ι₀ b' n).toRingHom.comp Φ.toRingHom = φ.toRingHom.comp σA.toRingHom :=
    congrArg AlgHom.toRingHom hΦq
  rw [hcomp] at hker hsurj
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsurj y
    exact ⟨σA x, hx⟩
  · ext a
    rw [RingHom.mem_ker]
    constructor
    · intro ha
      obtain ⟨s, hs⟩ := exists_sub_σA_mem_pow 𝔫 σ σA π mA hπσ hπ hπs hσ1 n a
      have hφs : φ (σA s) = 0 := by
        have : φ a = φ (a - σA s) + φ (σA s) := by rw [← map_add, sub_add_cancel]
        rw [ha, hkill _ hs, zero_add] at this
        exact this.symm
      have : s ∈ I ⊔ 𝔪 ^ n := by
        rw [← hker, RingHom.mem_ker]; exact hφs
      rw [sup_eq_left.mpr h𝔪I] at this
      have : a = (a - σA s) + σA s := by ring
      rw [this]
      exact Ideal.add_mem _ hs ‹s ∈ I›
    · exact hkill a

end Rigidity

end Langlands.CommutativeAlgebra.ApproximateQuotientRigidity
