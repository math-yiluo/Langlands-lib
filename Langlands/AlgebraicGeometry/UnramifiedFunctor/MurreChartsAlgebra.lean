import Mathlib

/-! # Commutative algebra for the construction of Murre's charts

* `exists_subalgebra_isLocalization`: an algebra of finite type over the localization
  `O = R_p` is the localization, at the image of `R \ p`, of an `R`-subalgebra of finite type.
* `exists_mem_basicOpen_subset`: an open subset of `Spec A` containing every prime disjoint
  from a submonoid `M` contains a basic open `D(m)` with `m ∈ M`.
* `exists_mem_basicOpen_disjoint`: for `C` noetherian, an open subset of `Spec C` meeting no
  prime disjoint from `N` is disjoint from some `D(n)` with `n ∈ N`.
* `exists_formallyUnramified_away`: if `M⁻¹A` is formally unramified over `R` and `A` is of
  finite type over `R`, then some `A[1/m]`, `m ∈ M`, is formally unramified over `R`. -/

universe u

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

/-- An algebra `B` of finite type over the localization `O = R_p` is the localization, at the
image of `R \ p`, of an `R`-subalgebra of `B` of finite type over `R`. -/
theorem exists_subalgebra_isLocalization {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (O : Type u) [CommRing O] [Algebra R O] [IsLocalization.AtPrime O p]
    (B : Type u) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower R O B]
    [hB : Algebra.FiniteType O B] :
    ∃ A : Subalgebra R B, Algebra.FiniteType R A ∧
      IsLocalization (p.primeCompl.map (algebraMap R A)) B := by
  obtain ⟨s, hs⟩ := hB.out
  refine ⟨Algebra.adjoin R (s : Set B), Algebra.FiniteType.adjoin_of_finite s.finite_toSet, ?_⟩
  set A := Algebra.adjoin R (s : Set B)
  have key : ∀ b : B, ∃ r ∈ p.primeCompl, algebraMap R B r * b ∈ A := by
    intro b
    have hb : b ∈ Algebra.adjoin O (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact ⟨1, p.primeCompl.one_mem, by simpa using Algebra.subset_adjoin hx⟩
    | algebraMap o =>
      obtain ⟨⟨a, w⟩, hw⟩ := IsLocalization.surj p.primeCompl o
      refine ⟨w, w.2, ?_⟩
      have : algebraMap R B w * algebraMap O B o = algebraMap R B a := by
        rw [IsScalarTower.algebraMap_apply R O B, IsScalarTower.algebraMap_apply R O B a,
          ← map_mul, mul_comm, hw]
      rw [this]
      exact A.algebraMap_mem a
    | add x y _ _ hx hy =>
      obtain ⟨r₁, hr₁, h₁⟩ := hx
      obtain ⟨r₂, hr₂, h₂⟩ := hy
      refine ⟨r₁ * r₂, p.primeCompl.mul_mem hr₁ hr₂, ?_⟩
      have : algebraMap R B (r₁ * r₂) * (x + y) = algebraMap R B r₂ * (algebraMap R B r₁ * x) +
          algebraMap R B r₁ * (algebraMap R B r₂ * y) := by
        rw [map_mul]; ring
      rw [this]
      exact A.add_mem (A.mul_mem (A.algebraMap_mem _) h₁) (A.mul_mem (A.algebraMap_mem _) h₂)
    | mul x y _ _ hx hy =>
      obtain ⟨r₁, hr₁, h₁⟩ := hx
      obtain ⟨r₂, hr₂, h₂⟩ := hy
      refine ⟨r₁ * r₂, p.primeCompl.mul_mem hr₁ hr₂, ?_⟩
      have : algebraMap R B (r₁ * r₂) * (x * y) =
          (algebraMap R B r₁ * x) * (algebraMap R B r₂ * y) := by
        rw [map_mul]; ring
      rw [this]
      exact A.mul_mem h₁ h₂
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    show IsUnit (algebraMap A B (algebraMap R A r))
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R O B]
    exact (IsLocalization.map_units O ⟨r, hr⟩).map _
  · intro b
    obtain ⟨r, hr, hb⟩ := key b
    refine ⟨⟨⟨_, hb⟩, ⟨algebraMap R A r, r, hr, rfl⟩⟩, ?_⟩
    show b * algebraMap A B (algebraMap R A r) = algebraMap R B r * b
    rw [← IsScalarTower.algebraMap_apply, mul_comm]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

/-- An open subset of `Spec A` containing every prime disjoint from `M` contains a basic open
`D(m)` with `m ∈ M`. -/
theorem exists_mem_basicOpen_subset {A : Type u} [CommRing A] (M : Submonoid A)
    {O : Set (PrimeSpectrum A)} (hO : IsOpen O)
    (hG : ∀ q : PrimeSpectrum A, Disjoint (M : Set A) q.asIdeal → q ∈ O) :
    ∃ m ∈ M, (PrimeSpectrum.basicOpen m : Set (PrimeSpectrum A)) ⊆ O := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Oᶜ).1 hO.isClosed_compl
  by_cases h : Disjoint (I : Set A) M
  · obtain ⟨q, hq, hIq, hqM⟩ := Ideal.exists_le_prime_disjoint I M h
    have h1 : (⟨q, hq⟩ : PrimeSpectrum A) ∈ Oᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus]
      exact hIq
    exact (h1 (hG ⟨q, hq⟩ hqM.symm)).elim
  · obtain ⟨m, hmI, hmM⟩ := Set.not_disjoint_iff.1 h
    refine ⟨m, hmM, fun x hx => ?_⟩
    by_contra hxO
    have : x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [← hI]
      exact hxO
    rw [PrimeSpectrum.mem_zeroLocus] at this
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hx (this hmI)

/-- For `C` noetherian, an open subset of `Spec C` containing no prime disjoint from `N` is
disjoint from some basic open `D(n)` with `n ∈ N`. -/
theorem exists_mem_basicOpen_disjoint {C : Type u} [CommRing C] [IsNoetherianRing C]
    (N : Submonoid C) {O : Set (PrimeSpectrum C)} (hO : IsOpen O)
    (hG : ∀ q ∈ O, ¬ Disjoint (N : Set C) q.asIdeal) :
    ∃ n ∈ N, Disjoint (PrimeSpectrum.basicOpen n : Set (PrimeSpectrum C)) O := by
  obtain ⟨t, ht⟩ :=
    PrimeSpectrum.isCompact_isOpen_iff.1 ⟨TopologicalSpace.NoetherianSpace.isCompact O, hO⟩
  have key : ∀ c ∈ t, ∃ n ∈ N, ∀ x : PrimeSpectrum C, n ∉ x.asIdeal → c ∈ x.asIdeal := by
    intro c hc
    by_cases h0 : ∃ n ∈ N, ∃ k : ℕ, n * c ^ k = 0
    · obtain ⟨n, hn, k, hk⟩ := h0
      refine ⟨n, hn, fun x hnx => ?_⟩
      have : n * c ^ k ∈ x.asIdeal := hk ▸ x.asIdeal.zero_mem
      rcases x.isPrime.mem_or_mem this with h | h
      · exact absurd h hnx
      · exact x.isPrime.mem_of_pow_mem k h
    · exfalso
      have hdisj : Disjoint ((⊥ : Ideal C) : Set C) (N ⊔ Submonoid.powers c : Submonoid C) := by
        rw [Set.disjoint_left]
        intro z hz hzN
        have hz0 : z = 0 := hz
        obtain ⟨y, hy, w, hw, rfl⟩ := Submonoid.mem_sup.1 hzN
        obtain ⟨k, rfl⟩ := hw
        exact h0 ⟨y, hy, k, hz0⟩
      obtain ⟨q, hq, -, hqN⟩ := Ideal.exists_le_prime_disjoint ⊥ _ hdisj
      have hcq : c ∉ q := fun hcq => Set.disjoint_left.1 hqN hcq
        (Submonoid.mem_sup_right (Submonoid.mem_powers c))
      have hqO : (⟨q, hq⟩ : PrimeSpectrum C) ∈ O := by
        rw [← ht]
        intro hz
        rw [PrimeSpectrum.mem_zeroLocus] at hz
        exact hcq (hz hc)
      refine hG _ hqO (Set.disjoint_left.2 fun z hzN hzq => ?_)
      exact Set.disjoint_left.1 hqN hzq (Submonoid.mem_sup_left hzN)
  choose! f hfN hf using key
  refine ⟨∏ c ∈ t, f c, prod_mem fun c hc => hfN c hc, ?_⟩
  rw [Set.disjoint_left]
  intro x hx hxO
  rw [← ht] at hxO
  apply hxO
  rw [PrimeSpectrum.mem_zeroLocus]
  intro c hc
  apply hf c hc x
  intro hfc
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hc
  apply (PrimeSpectrum.mem_basicOpen _ _).1 hx
  rw [hk]
  exact x.asIdeal.mul_mem_right _ hfc

section Unramified

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] (M : Submonoid A) [IsLocalization M B]

/-- If `M⁻¹A` is formally unramified over `R`, then `A` is unramified over `R` at every prime
disjoint from `M`. -/
theorem mem_unramifiedLocus [Algebra.FormallyUnramified R B] (q : PrimeSpectrum A)
    (hq : Disjoint (M : Set A) q.asIdeal) : q ∈ Algebra.unramifiedLocus R A := by
  have hle : M ≤ q.asIdeal.primeCompl := fun m hm hmq => Set.disjoint_left.1 hq hm hmq
  let L := Localization.AtPrime q.asIdeal
  let : Algebra B L := IsLocalization.localizationAlgebraOfSubmonoidLe B L M _ hle
  have : IsScalarTower A B L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B L M _ hle
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap A B)) L :=
    IsLocalization.isLocalization_of_submonoid_le B L M _ hle
  have : Algebra.FormallyUnramified B L :=
    Algebra.FormallyUnramified.of_isLocalization (q.asIdeal.primeCompl.map (algebraMap A B))
  have : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A B, ← IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply R A L]
  exact Algebra.FormallyUnramified.comp R B L

/-- If `M⁻¹A` is formally unramified over `R` and `A` is of finite type over `R`, then
`A[1/m]` is formally unramified over `R` for some `m ∈ M`. -/
theorem exists_formallyUnramified_away [Algebra.FiniteType R A]
    [Algebra.FormallyUnramified R B] :
    ∃ m ∈ M, Algebra.FormallyUnramified R (Localization.Away m) := by
  obtain ⟨m, hm, hsub⟩ := exists_mem_basicOpen_subset M Algebra.isOpen_unramifiedLocus
    (fun q hq => mem_unramifiedLocus (R := R) (B := B) M q hq)
  exact ⟨m, hm, Algebra.basicOpen_subset_unramifiedLocus_iff.1 hsub⟩

end Unramified

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
