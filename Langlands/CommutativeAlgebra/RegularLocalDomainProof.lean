import Langlands.CommutativeAlgebra.RegularLocalDomainStatement
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Proof: regular local rings are domains -/

universe u

open IsLocalRing

namespace Langlands.CommutativeAlgebra

namespace RegularLocalDomain

variable {R : Type*} [CommRing R]

/-- If `x ∈ 𝔪 \ 𝔪²` in a Noetherian local ring, the maximal ideal of `R ⧸ (x)` needs at
least one generator fewer than `𝔪`. -/
theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  let k := ResidueField R
  let v : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩
  have hv : v ≠ 0 := by
    simpa [v, Ideal.toCotangent_eq_zero] using hx2
  let K : Submodule k (CotangentSpace R) := k ∙ v
  have hK : Module.finrank k K = 1 := finrank_span_singleton hv
  have hW : Module.finrank k (CotangentSpace R ⧸ K) + 1 =
      Module.finrank k (CotangentSpace R) := by
    rw [← hK]; exact Submodule.finrank_quotient_add_finrank K
  let b := Module.finBasis k (CotangentSpace R ⧸ K)
  have hsurj : Function.Surjective
      (fun z : maximalIdeal R => K.mkQ ((maximalIdeal R).toCotangent z)) :=
    (Submodule.mkQ_surjective K).comp (maximalIdeal R).toCotangent_surjective
  let y : Fin (Module.finrank k (CotangentSpace R ⧸ K)) → maximalIdeal R :=
    fun i => Function.surjInv hsurj (b i)
  have hy : ∀ i, K.mkQ ((maximalIdeal R).toCotangent (y i)) = b i :=
    fun i => Function.surjInv_eq hsurj (b i)
  let s : Set (maximalIdeal R) := insert ⟨x, hx⟩ (Set.range y)
  have hspan : Submodule.span R s = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff]
    set U := Submodule.span k ((maximalIdeal R).toCotangent '' s)
    have hvU : v ∈ U := Submodule.subset_span ⟨⟨x, hx⟩, Set.mem_insert _ _, rfl⟩
    have hKU : K ≤ U := (Submodule.span_singleton_le_iff_mem _ _).mpr hvU
    have hmap : U.map K.mkQ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨(maximalIdeal R).toCotangent (y i),
        Submodule.subset_span ⟨y i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩, hy i⟩
    rw [Submodule.map_mkQ_eq_top, sup_of_le_right hKU] at hmap
    exact hmap
  have hm : maximalIdeal R = Ideal.span (insert x (Set.range fun i => (y i : R))) := by
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
    refine this.symm.trans ?_
    rw [Set.image_insert_eq, ← Set.range_comp]
    rfl
  let f : Fin (Module.finrank k (CotangentSpace R ⧸ K)) → R ⧸ Ideal.span {x} :=
    fun i => Ideal.Quotient.mk _ (y i : R)
  have hS : maximalIdeal (R ⧸ Ideal.span {x}) = Ideal.span (Set.range f) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective]
    refine (congrArg (Ideal.map _) hm).trans ?_
    rw [Ideal.map_span, Set.image_insert_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x),
      Ideal.span_insert_zero, ← Set.range_comp]
    rfl
  have hcard : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤
      Module.finrank k (CotangentSpace R ⧸ K) := by
    rw [hS]
    calc (Ideal.span (Set.range f)).spanFinrank ≤ (Set.range f).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range f)
      _ ≤ (Set.univ : Set (Fin (Module.finrank k (CotangentSpace R ⧸ K)))).ncard := by
          rw [← Set.image_univ]; exact Set.ncard_image_le Set.finite_univ
      _ = Module.finrank k (CotangentSpace R ⧸ K) := by simp
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R, ← hW]
  omega

/-- Prime avoidance: if `𝔪 ≠ 𝔪²` and `𝔪` is not a minimal prime, some element of `𝔪` lies
neither in `𝔪²` nor in any minimal prime. -/
theorem exists_mem_maximalIdeal_avoiding [IsLocalRing R] [IsNoetherianRing R]
    (hm2 : maximalIdeal R ≠ maximalIdeal R ^ 2) (hmin : maximalIdeal R ∉ minimalPrimes R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  have hfin : (insert (maximalIdeal R ^ 2) (minimalPrimes R)).Finite :=
    (minimalPrimes.finite_of_isNoetherianRing R).insert _
  have hne : maximalIdeal R ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self two_ne_zero)
  have key := Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite (M := maximalIdeal R) hfin
    (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
    (fun I hI h1 _ => by
      rcases Set.mem_insert_iff.mp hI with h | h
      · exact absurd h h1
      · exact h.1.1) hne hne
  have hnot : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ insert (maximalIdeal R ^ 2) (minimalPrimes R), (I : Set R)) := by
    rw [key]
    rintro (h | h)
    · exact hm2 h
    · exact hmin h
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_iUnion, not_exists, Set.mem_insert_iff] at hx
  refine ⟨x, hxm, fun h => hx _ (Or.inl rfl) h, fun p hp h => hx p (Or.inr hp) h⟩

/-- If `x ∈ 𝔪` lies in no minimal prime of a Noetherian local ring `R` and `(x)` is prime,
then `R` is a domain. -/
theorem isDomain_of_isPrime_span_singleton [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, x ∉ p)
    (hprime : (Ideal.span {x}).IsPrime) : IsDomain R := by
  obtain ⟨p, hp, hle⟩ := Ideal.exists_minimalPrimes_le (show ⊥ ≤ Ideal.span {x} from bot_le)
  have hpP : p.IsPrime := hp.1.1
  have hxp : x ∉ p := hmin p hp
  have hle' : p ≤ maximalIdeal R • p := by
    intro y hy
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp (hle hy)
    have hr : r ∈ p := (hpP.mem_or_mem hy).resolve_right hxp
    simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem_smul hx hr
  have hbot : p = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
    p.fg_of_isNoetherianRing hle' (maximalIdeal_le_jacobson _)
  have : (⊥ : Ideal R).IsPrime := hbot ▸ hpP
  exact IsDomain.of_bot_isPrime R

/-- The induction on the minimal number of generators of the maximal ideal. -/
theorem isDomain_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ hn
  have hreg : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `𝔪 = 0`, so `⊥ = 𝔪` is prime.
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp
        (hn.trans h0)
    have : (⊥ : Ideal R).IsPrime := hbot ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  · have hm2 : maximalIdeal R ≠ maximalIdeal R ^ 2 := by
      intro h
      have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := by
        rw [smul_eq_mul, ← pow_two, ← h]
      have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing hle (maximalIdeal_le_jacobson _)
      rw [this, Submodule.spanFinrank_bot] at hn
      omega
    have hmin : maximalIdeal R ∉ minimalPrimes R := by
      intro h
      have h0 : (maximalIdeal R).height = 0 := Ideal.height_eq_zero_iff.mpr h
      have hdim0 := maximalIdeal_height_eq_ringKrullDim (R := R)
      rw [h0] at hdim0
      rw [← hdim0, hn] at hreg
      norm_cast at hreg
      omega
    obtain ⟨x, hx, hx2, hxmin⟩ := exists_mem_maximalIdeal_avoiding hm2 hmin
    have hxtop : Ideal.span {x} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal x).mp hx
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxtop
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hdrop := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have hdim : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
      have := Ideal.height_le_ringKrullDim_quotient_add_one (p := maximalIdeal R) hx
      rwa [maximalIdeal_height_eq_ringKrullDim] at this
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
      apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
        (ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial :
          ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊥)
      rw [← hd, ← hreg] at hdim
      rw [← hd]
      have h1 : (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : ℕ∞) ≤ d + 1 := by
        have := (Nat.cast_le (α := WithBot ℕ∞)).mpr hdrop
        exact_mod_cast this.trans hdim
      have h2 : ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : ℕ∞) ≤ d := by
        push_cast at h1
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1
      exact_mod_cast h2
    have : IsDomain (R ⧸ Ideal.span {x}) := ih _ (by omega) _ rfl
    exact isDomain_of_isPrime_span_singleton hx hxmin
      ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)

end RegularLocalDomain

open RegularLocalDomain in
/-- Every regular local ring is a domain (Stacks Project, Lemma 10.106.2, Tag 00NP). -/
theorem regularLocalDomain : RegularLocalDomainStatement.{u} := by
  intro R _ hR
  exact isDomain_of_spanFinrank_eq _ R rfl

end Langlands.CommutativeAlgebra
