import Langlands.GaloisCohomology.Global.PoitouTate.NineTermStatement
import Langlands.GaloisCohomology.Global.PoitouTate.NineTermProof
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Ratio
import Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality

/-!
# Counting `H²(G_S, M)` with Poitou–Tate

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`
containing the places above `N ≥ 1`, and `M` a finite smooth `G_S`-module killed by `N`, with dual
`M' = Hom(M, μ_N)`. The end of the nine-term sequence of Poitou–Tate,
`H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨ → 0` with kernel `Ш²_S(M)` on the left, gives
`#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H²(K_v, M) · ∏_{w real} #H²(K_w, M)`
(`card_cohomology_two_mul_card_dual_zero`), by the nine-term sequence of Poitou–Tate
(`poitouTateNineTermStatement`).
With local duality at the places of `S`, `#H²(K_v, M) = #H⁰(K_v, M')`
(`card_cohomology_two_localModule_eq`), and when `N` is odd or `K` totally complex (no contribution
of the real places):
`#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H⁰(K_v, M')`
(`card_cohomology_two_mul_card_dual_zero_eq_prod`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Counting

/-- For `0 → ker f → A → B → C → 0` exact with `A`, `B` finite: `#A · #C = #ker f · #B`. -/
theorem card_mul_card_eq_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Finite A] [Finite B] (f : A →+ B) (g : B →+ C) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Nat.card A * Nat.card C = Nat.card f.ker * Nat.card B := by
  have hA := card_eq_card_ker_mul_card_range f.toIntLinearMap
  have hB := card_eq_card_ker_mul_card_range g.toIntLinearMap
  have hker : LinearMap.ker g.toIntLinearMap = LinearMap.range f.toIntLinearMap := by
    ext y
    exact hfg y
  have hrange : Nat.card (LinearMap.range g.toIntLinearMap) = Nat.card C := by
    rw [LinearMap.range_eq_top.2 hg]
    exact Nat.card_congr (Equiv.Set.univ C)
  rw [hker, hrange] at hB
  have hk : Nat.card (LinearMap.ker f.toIntLinearMap) = Nat.card f.ker := rfl
  rw [hA, hB, hk]
  ring

/-- A prime ideal containing a positive integer `n` contains a prime factor of `n`. -/
theorem exists_prime_dvd_mem_of_natCast_mem {R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime]
    {n : ℕ} (hn : (n : R) ∈ I) (hn0 : n ≠ 0) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : R) ∈ I := by
  induction n using Nat.recOnPrimePow with
  | zero => exact absurd rfl hn0
  | one =>
    exact absurd (I.eq_top_of_isUnit_mem hn (by simp)) Ideal.IsPrime.ne_top'
  | prime_pow_mul a p k hp hpa hk ih =>
    rw [Nat.cast_mul, Nat.cast_pow] at hn
    rcases Ideal.IsPrime.mem_or_mem ‹_› hn with h | h
    · exact ⟨p, hp, dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') a,
        Ideal.IsPrime.mem_of_pow_mem ‹_› k h⟩
    · obtain ⟨q, hq, hqa, hqI⟩ := ih h (fun h0 => hn0 (by rw [h0, mul_zero]))
      exact ⟨q, hq, dvd_mul_of_dvd_right hqa _, hqI⟩

variable {K : Type u} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

omit [NumberField K] in
/-- If `N` kills `X` and the places above `N` lie in `S`, so do the places above `#X`. -/
theorem mem_of_natCard_mem_of_nsmul_eq_zero {N : ℕ}
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {X : Type*} [AddCommGroup X] [Finite X] (h : ∀ x : X, N • x = 0) :
    ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card X : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  obtain ⟨p, hp, hpX, hpv⟩ := exists_prime_dvd_mem_of_natCast_mem hv Nat.card_pos.ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpX
  have hpN : p ∣ N := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero (h x)
  obtain ⟨c, rfl⟩ := hpN
  refine hS v ?_
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpv

end Counting

section Local

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- The local cohomology of a finite module at a finite place is finite. -/
theorem finite_cohomology_localModule (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (cohomology (localModule ι M v) n) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  let := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  exact Local.finite_cohomology (K := v.adicCompletion K)
    (Ksep := AlgebraicClosure (v.adicCompletion K)) (localModule ι M v)
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') n

/-- The local cohomology of a finite module at a real place is finite in degrees `≤ 2`. -/
theorem finite_cohomology_realLocalModule (w : {w : InfinitePlace K // w.IsReal}) (n : ℕ)
    (hn : n ≤ 2) : Finite (cohomology (realLocalModule ι M w.1) n) :=
  finite_cohomology_of_isReal w.1 w.2 _ n hn

end Local

section NineTerm

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

/-- **The count of `H²` from Poitou–Tate.** For `M` killed by `N`:
`#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H²(K_v, M) · ∏_{w real} #H²(K_w, M)`. -/
theorem card_cohomology_two_mul_card_dual_zero
    (N : ℕ) [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) :
    haveI : Fintype S := Fintype.ofFinite S
    Nat.card (cohomology M 2) * Nat.card (cohomology (PoitouTate.dual N M) 0) =
      Nat.card (sha ι M 2) * ((∏ v : S, Nat.card (cohomology (localModule ι M v) 2)) *
        ∏ w : {w : InfinitePlace K // w.IsReal},
          Nat.card (cohomology (realLocalModule ι M w.1) 2)) := by
  classical
  let : Fintype S := Fintype.ofFinite S
  have hNT := poitouTateNineTermStatement K Ω S ι N hS M hM
  have hSM := mem_of_natCard_mem_of_nsmul_eq_zero hS hM
  have := finite_cohomology_of_le_two M hSM 2 le_rfl
  have : Finite (PoitouTate.dualizingModule K Ω S N) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))))
  have : Finite (PoitouTate.dual N M) := finite_dualRep
  have : Finite (cohomology (PoitouTate.dual N M) 0) := finite_cohomology_zero _
  have : ∀ v : S, Finite (cohomology (localModule ι M v) 2) := fun v =>
    finite_cohomology_localModule ι M v 2
  have : ∀ w : {w : InfinitePlace K // w.IsReal}, Finite (cohomology (realLocalModule ι M w.1) 2) :=
    fun w => finite_cohomology_realLocalModule ι M w 2 le_rfl
  have : Finite (PoitouTate.LocalTerm ι M 2) := inferInstance
  have hc := card_mul_card_eq_of_exact (PoitouTate.loc ι M 2)
    (PoitouTate.locDual ι N M (show 2 + 0 = 2 from rfl)) hNT.exact_loc_locDual_two
    hNT.surjective_locDual_two
  rw [QZ.card_hom] at hc
  have hker : (PoitouTate.loc ι M 2).ker = sha ι M 2 := by
    ext x
    rw [AddMonoidHom.mem_ker]
    exact (PoitouTate.mem_sha_iff_loc_eq_zero ι M x).symm
  rw [hker] at hc
  rw [hc, Nat.card_prod, Nat.card_pi, Nat.card_pi]

end NineTerm

section LocalDuality

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

/-- **Local duality, the count.** At a place `v ∈ S`, `#H²(K_v, M) = #H⁰(K_v, M')` for `M` killed
by `N`, `M' = Hom(M, μ_N)`. -/
theorem card_cohomology_two_localModule_eq (N : ℕ) [NeZero N]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) (v : S) :
    Nat.card (cohomology (localModule ι M v) 2) =
      Nat.card (cohomology (localModule ι (PoitouTate.dual N M) v) 0) := by
  have : Finite (PoitouTate.dualizingModule K Ω S N) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))))
  have : Finite (PoitouTate.dual N M) := finite_dualRep
  have : Finite (cohomology (localModule ι (PoitouTate.dual N M) v) 0) :=
    finite_cohomology_localModule ι (PoitouTate.dual N M) v 0
  rw [Nat.card_congr (Equiv.ofBijective _ (bijective_ptLocalPairing_two ι N M hS hM v)),
    QZ.card_hom]

/-- **The count of `H²` with the local duals.** If `N` is odd or `K` is totally complex, for `M`
killed by `N`: `#H²(G_S, M) · #H⁰(G_S, M') = #Ш²_S(M) · ∏_{v ∈ S} #H⁰(K_v, M')`. -/
theorem card_cohomology_two_mul_card_dual_zero_eq_prod
    (N : ℕ) [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd N ∨ IsTotallyComplex K)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) :
    haveI : Fintype S := Fintype.ofFinite S
    Nat.card (cohomology M 2) * Nat.card (cohomology (PoitouTate.dual N M) 0) =
      Nat.card (sha ι M 2) *
        ∏ v : S, Nat.card (cohomology (localModule ι (PoitouTate.dual N M) v) 0) := by
  have hc := card_cohomology_two_mul_card_dual_zero ι N hS M hM
  have hreal : ∏ w : {w : InfinitePlace K // w.IsReal},
      Nat.card (cohomology (realLocalModule ι M w.1) 2) = 1 :=
    Finset.prod_eq_one fun w _ => by
      rcases hK with ho | hc
      · have : Subsingleton (cohomology (realLocalModule ι M w.1) 2) :=
          ⟨fun x y => (eq_zero_cohomology_closureGalois_of_odd w.1 w.2 _ ho (fun a => hM a)
            (by norm_num) x).trans (eq_zero_cohomology_closureGalois_of_odd w.1 w.2 _ ho
              (fun a => hM a) (by norm_num) y).symm⟩
        exact Nat.card_unique
      · exact absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (hc.isComplex w.1))
  rw [hreal, mul_one] at hc
  rw [hc, Finset.prod_congr rfl fun v _ => card_cohomology_two_localModule_eq ι N hS M hM v]

end LocalDuality

end

end Langlands.GaloisCohomology

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology

universe u

noncomputable section

section Counting

/-- For `A → B → C` exact at `B`: `#B = #(image of A) · #(image of B)`. -/
theorem card_eq_card_range_mul_card_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (h : Function.Exact f g) :
    Nat.card B = Nat.card f.range * Nat.card g.range := by
  have hker : g.ker = f.range := AddSubgroup.ext fun y => (h y).trans Iff.rfl
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hker, mul_comm]

/-- **The count along an exact sequence** `0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → A₇ → 0`:
`#A₁ · #A₃ · #A₅ · #A₇ = #A₂ · #A₄ · #A₆`. -/
theorem card_mul_card_eq_of_exact_seven {A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Type*} [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅] [AddCommGroup A₆]
    [AddCommGroup A₇] (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅)
    (f₅ : A₅ →+ A₆) (f₆ : A₆ →+ A₇) (h₁ : Function.Injective f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ f₃) (h₄ : Function.Exact f₃ f₄) (h₅ : Function.Exact f₄ f₅)
    (h₆ : Function.Exact f₅ f₆) (h₇ : Function.Surjective f₆) :
    Nat.card A₁ * Nat.card A₃ * Nat.card A₅ * Nat.card A₇ =
      Nat.card A₂ * Nat.card A₄ * Nat.card A₆ := by
  have e₁ : Nat.card A₁ = Nat.card f₁.range :=
    Nat.card_congr (Equiv.ofInjective f₁ h₁) |>.trans rfl
  have e₇ : Nat.card A₇ = Nat.card f₆.range := by
    rw [AddMonoidHom.range_eq_top.2 h₇]
    exact (Nat.card_congr (Equiv.Set.univ A₇)).symm
  rw [e₁, e₇, card_eq_card_range_mul_card_range f₁ f₂ h₂, card_eq_card_range_mul_card_range f₂ f₃ h₃,
    card_eq_card_range_mul_card_range f₃ f₄ h₄, card_eq_card_range_mul_card_range f₄ f₅ h₅,
    card_eq_card_range_mul_card_range f₅ f₆ h₆]
  ring

end Counting

end

end Langlands.GaloisCohomology
