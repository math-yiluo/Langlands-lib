import Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionStatement
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Polynomial.Basic

/-! # Resolving the local problem at a minimal prime: proof

Proves `DimZeroResolutionStatement` (Stacks Lemmas 16.9.3 and 16.9.4, Tags 07F9 and 07FA).
The resolving algebra `B` is built directly as a finitely generated `R`-subalgebra of
`C[X]_X × A × Λ`, where `C` is the smooth algebra supplied by property PT for `Λ_q`. Two
elements of `B` are shown to lie in `H_{B/R}` by identifying the corresponding localizations
of `B` with `C[X]_X` and with `A_a`. See the paired Markdown for the full argument. -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace DimZeroResolutionProof

open Polynomial

/-- If `B` is finitely presented over `R` and `B_e` is smooth over `R`, then `e ∈ H_{B/R}`. -/
theorem mem_singularIdeal_of_smooth {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (e : B) (h : Algebra.Smooth R (Localization.Away e)) :
    e ∈ singularIdeal R B := by
  have hsub := (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := B) (f := e)).2 h
  rw [singularIdeal, PrimeSpectrum.mem_vanishingIdeal]
  intro x hx
  by_contra hex
  exact hx (hsub ((PrimeSpectrum.mem_basicOpen e x).2 hex))

/-- If `A` is finitely presented over `R` and `a ∈ H_{A/R}`, then `A_a` is smooth over `R`. -/
theorem smooth_away_of_mem_singularIdeal {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] {a : A} (ha : a ∈ singularIdeal R A) :
    Algebra.Smooth R (Localization.Away a) := by
  refine (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := A) (f := a)).1 ?_
  intro x hx
  by_contra hns
  exact (PrimeSpectrum.mem_basicOpen a x).1 hx
    ((PrimeSpectrum.mem_vanishingIdeal _ _).1 ha x hns)

/-- If an `R`-algebra map `φ : B → Y` to a smooth `R`-algebra exhibits `Y` as the localization
of `B` away from `e`, then `B_e` is smooth over `R`. -/
theorem smooth_away_of_isLocalization {R B Y : Type*} [CommRing R] [CommRing B] [CommRing Y]
    [Algebra R B] [Algebra R Y] [Algebra.Smooth R Y] (φ : B →ₐ[R] Y) (e : B)
    (hunit : IsUnit (φ e))
    (hsurj : ∀ y : Y, ∃ (n : ℕ) (b : B), y * φ e ^ n = φ b)
    (hker : ∀ b : B, φ b = 0 → ∃ n : ℕ, e ^ n * b = 0) :
    Algebra.Smooth R (Localization.Away e) := by
  let : Algebra B Y := φ.toRingHom.toAlgebra
  have : IsScalarTower R B Y := IsScalarTower.of_algebraMap_eq (fun r => (φ.commutes r).symm)
  have : IsLocalization.Away e Y := by
    refine IsLocalization.Away.mk e hunit hsurj (fun a b hab => ?_)
    obtain ⟨n, hn⟩ := hker (a - b) (by
      rw [map_sub]
      exact sub_eq_zero.2 hab)
    exact ⟨n, by rw [mul_sub] at hn; exact sub_eq_zero.1 hn⟩
  exact Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers e) Y (Localization.Away e)).restrictScalars R)

/-- For a prime `q` of a Noetherian ring `Λ`, one element `s ∉ q` annihilates the kernel of
`Λ → Λ_q`. -/
theorem exists_mul_eq_zero_of_algebraMap_eq_zero {Λ : Type*} [CommRing Λ] [IsNoetherianRing Λ]
    (q : Ideal Λ) [q.IsPrime] :
    ∃ s ∉ q, ∀ l : Λ, algebraMap Λ (Localization.AtPrime q) l = 0 → s * l = 0 := by
  let K := RingHom.ker (algebraMap Λ (Localization.AtPrime q))
  have hnot : (⟨q, inferInstance⟩ : PrimeSpectrum Λ) ∉ Module.support Λ K := by
    rw [Module.notMem_support_iff']
    rintro ⟨l, hl⟩
    obtain ⟨⟨m, hm⟩, hml⟩ :=
      (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) l).1 hl
    exact ⟨m, hm, Subtype.ext (by simpa using hml)⟩
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨s, hs, hsq⟩ := SetLike.not_le_iff_exists.1 hnot
  refine ⟨s, hsq, fun l hl => ?_⟩
  have := Module.mem_annihilator.1 hs ⟨l, hl⟩
  simpa using congrArg Subtype.val this

/-- At a minimal prime `q`, every element of `q` becomes nilpotent in `Λ_q`. -/
theorem exists_pow_algebraMap_eq_zero {Λ : Type*} [CommRing Λ] {q : Ideal Λ} [q.IsPrime]
    (hq : q ∈ minimalPrimes Λ) {x : Λ} (hx : x ∈ q) :
    ∃ n : ℕ, algebraMap Λ (Localization.AtPrime q) (x ^ (n + 1)) = 0 := by
  have := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes q hq
    (Localization.AtPrime q)
  have hnil : IsNilpotent (algebraMap Λ (Localization.AtPrime q) x) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJm : J = IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
      congrArg PrimeSpectrum.asIdeal
        (Subsingleton.elim (⟨J, hJ⟩ : PrimeSpectrum _) ⟨IsLocalRing.maximalIdeal _, inferInstance⟩)
    rw [hJm]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q x).2 hx
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, by rw [map_pow, pow_succ, hn, zero_mul]⟩

/-- If `x ^ k * y = 0` and `k ≤ m`, then `x ^ m * y = 0`. -/
theorem pow_mul_eq_zero_of_le {M : Type*} [CommMonoidWithZero M] {x y : M} {k m : ℕ}
    (h : x ^ k * y = 0) (hkm : k ≤ m) : x ^ m * y = 0 := by
  rw [← Nat.sub_add_cancel hkm, pow_add, mul_assoc, h, mul_zero]

/-- An induction principle for `C[X]_X`: a property closed under sums and products, holding on
the image of `R`, on `X`, on generators of `C` over `R`, and descending along multiplication by
powers of `X`, holds everywhere. -/
theorem away_X_induction {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] (tc : Finset C)
    (htc : Algebra.adjoin R (tc : Set C) = ⊤) (Good : Localization.Away (X : C[X]) → Prop)
    (hadd : ∀ x y, Good x → Good y → Good (x + y))
    (hmul : ∀ x y, Good x → Good y → Good (x * y))
    (halg : ∀ r : R, Good (algebraMap R _ r))
    (hT : Good (algebraMap C[X] _ X)) (hc : ∀ c ∈ tc, Good (algebraMap C _ c))
    (hdiv : ∀ y (m : ℕ), Good (y * algebraMap C[X] _ X ^ m) → Good y)
    (y : Localization.Away (X : C[X])) : Good y := by
  let S : Subalgebra R (Localization.Away (X : C[X])) :=
    { carrier := {y | Good y}
      mul_mem' := fun hx hy => hmul _ _ hx hy
      add_mem' := fun hx hy => hadd _ _ hx hy
      algebraMap_mem' := halg }
  have hC : ∀ c : C, Good (algebraMap C _ c) := by
    have hle : Algebra.adjoin R (tc : Set C) ≤
        S.comap (IsScalarTower.toAlgHom R C (Localization.Away (X : C[X]))) :=
      Algebra.adjoin_le (fun c hc' => hc c hc')
    intro c
    have hc'' : c ∈ Algebra.adjoin R (tc : Set C) := by rw [htc]; trivial
    exact hle hc''
  have hP : ∀ p : C[X], Good (algebraMap C[X] _ p) := by
    intro p
    induction p using Polynomial.induction_on with
    | C c =>
      have h := hC c
      rwa [IsScalarTower.algebraMap_apply C C[X] (Localization.Away (X : C[X])),
        Polynomial.algebraMap_eq] at h
    | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
    | monomial n c ih =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact hmul _ _ ih hT
  obtain ⟨m, p, hp⟩ := IsLocalization.Away.surj (X : C[X]) y
  exact hdiv y m (hp ▸ hP p)

end DimZeroResolutionProof

open DimZeroResolutionProof Polynomial in
/-- Stacks Lemmas 16.9.3 (07F9) and 16.9.4 (07FA), in the form of
`DimZeroResolutionStatement`. -/
theorem dimZeroResolution : DimZeroResolutionStatement.{u} := by
  intro R A Λ _ _ _ _ _ _ _ _ f q _ hhA hq hPT
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  -- generators of `H_{A/R}`
  obtain ⟨t, ht⟩ : (singularIdeal R A).FG := IsNoetherian.noetherian _
  have ht' : Ideal.span (t : Set A) = singularIdeal R A := ht
  have htH : ∀ a ∈ t, a ∈ singularIdeal R A := fun a ha => by
    rw [← ht']; exact Ideal.subset_span ha
  -- an element `s ∉ q` killing the kernel of `Λ → Λ_q`
  obtain ⟨s, hsq, hs⟩ := exists_mul_eq_zero_of_algebraMap_eq_zero q
  have hfq : ∀ a ∈ t, f a ∈ q := fun a ha =>
    hhA (Ideal.le_radical (Ideal.mem_map_of_mem f (htH a ha)))
  have hn : ∀ a ∈ t, ∃ n : ℕ,
      algebraMap Λ (Localization.AtPrime q) (f a ^ (n + 1)) = 0 :=
    fun a ha => exists_pow_algebraMap_eq_zero hq (hfq a ha)
  choose! n hn using hn
  have hsn : ∀ a ∈ t, s * f a ^ (n a + 1) = 0 := fun a ha => hs _ (hn a ha)
  have hzero : ∀ a ∈ t, ∀ y : Λ, algebraMap Λ (Localization.Away (f a)) (s * y) = 0 := by
    intro a ha y
    refine (IsLocalization.map_eq_zero_iff (Submonoid.powers (f a)) _ (s * y)).2
      ⟨⟨f a ^ (n a + 1), n a + 1, rfl⟩, ?_⟩
    change f a ^ (n a + 1) * (s * y) = 0
    rw [← mul_assoc, mul_comm (f a ^ (n a + 1)) s, hsn a ha, zero_mul]
  -- property PT for `R → Λ_q`
  obtain ⟨C, _, _, hCsm, g, ψ, hψ⟩ :=
    hPT A ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q)).comp f)
  have hψa : ∀ a, ψ (g a) = algebraMap Λ (Localization.AtPrime q) (f a) := fun a => by
    simpa using AlgHom.congr_fun hψ a
  obtain ⟨tc, htc⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R C).FG)
  obtain ⟨⟨u, hu⟩, hint⟩ := IsLocalization.exist_integer_multiples q.primeCompl tc ψ
  have hl : ∀ c ∈ tc, ∃ l : Λ, algebraMap Λ (Localization.AtPrime q) l =
      algebraMap Λ (Localization.AtPrime q) u * ψ c := fun c hc => by
    obtain ⟨l, hl⟩ := hint c hc
    exact ⟨l, by rw [hl, Algebra.smul_def]⟩
  choose! l hl using hl
  have hμq : s * u ∉ q := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hsq hu
  have hμunit : IsUnit (algebraMap Λ (Localization.AtPrime q) (s * u)) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨s * u, hμq⟩ : q.primeCompl)
  -- the smooth algebra `D = C[X]_X` and its map to `Λ_q`, `X ↦ s u`
  let ψX : C[X] →ₐ[R] Localization.AtPrime q :=
    Polynomial.aevalTower ψ (algebraMap Λ (Localization.AtPrime q) (s * u))
  have hψXX : ψX X = algebraMap Λ (Localization.AtPrime q) (s * u) :=
    Polynomial.aevalTower_X _ _
  obtain ⟨ψD, hψDC, hψDT⟩ : ∃ ψD : Localization.Away (X : C[X]) →ₐ[R] Localization.AtPrime q,
      (∀ c : C, ψD (algebraMap C _ c) = ψ c) ∧
        ψD (algebraMap C[X] _ X) = algebraMap Λ (Localization.AtPrime q) (s * u) := by
    refine ⟨IsLocalization.Away.liftAlgHom (X : C[X]) (f := ψX) (by rw [hψXX]; exact hμunit),
      fun c => ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply C C[X] (Localization.Away (X : C[X])),
        IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
        Polynomial.algebraMap_apply]
      exact Polynomial.aevalTower_C _ _ _
    · rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
      exact hψXX
  have : Algebra.FormallySmooth R C[X] := Algebra.FormallySmooth.comp R C C[X]
  have : Algebra.Smooth R C[X] := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth C[X] (Localization.Away (X : C[X])) :=
    Algebra.Smooth.of_isLocalization_Away X
  have : Algebra.Smooth R (Localization.Away (X : C[X])) :=
    Algebra.Smooth.comp R C[X] (Localization.Away (X : C[X]))
  -- the ambient product `D × A × Λ` and the subalgebra `P` of compatible triples
  obtain ⟨P, hP⟩ : ∃ P : Subalgebra R (Localization.Away (X : C[X]) × A × Λ), ∀ x, x ∈ P ↔
      (ψD x.1 = algebraMap Λ (Localization.AtPrime q) x.2.2 ∧
        ∀ a ∈ t, algebraMap Λ (Localization.Away (f a)) (f x.2.1) =
          algebraMap Λ (Localization.Away (f a)) x.2.2) := by
    refine ⟨
      { carrier := {x | ψD x.1 = algebraMap Λ (Localization.AtPrime q) x.2.2 ∧
            ∀ a ∈ t, algebraMap Λ (Localization.Away (f a)) (f x.2.1) =
              algebraMap Λ (Localization.Away (f a)) x.2.2}
        mul_mem' := ?_
        add_mem' := ?_
        algebraMap_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      refine ⟨?_, fun a ha => ?_⟩
      · simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hx1, hy1]
      · simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hx2 a ha, hy2 a ha]
    · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      refine ⟨?_, fun a ha => ?_⟩
      · simp only [Prod.fst_add, Prod.snd_add, map_add, hx1, hy1]
      · simp only [Prod.fst_add, Prod.snd_add, map_add, hx2 a ha, hy2 a ha]
    · intro r
      refine ⟨?_, fun a ha => ?_⟩
      · simp only [Prod.algebraMap_apply, AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply R Λ (Localization.AtPrime q) r
      · simp only [Prod.algebraMap_apply, AlgHom.commutes]
  -- the diagonal map `A → D × A × Λ`
  let ιE : A →ₐ[R] Localization.Away (X : C[X]) × A × Λ :=
    ((IsScalarTower.toAlgHom R C (Localization.Away (X : C[X]))).comp g).prod
      ((AlgHom.id R A).prod f)
  let T : Localization.Away (X : C[X]) := algebraMap C[X] _ X
  let e1 : Localization.Away (X : C[X]) × A × Λ := (T, 0, s * u)
  let β : C → Localization.Away (X : C[X]) × A × Λ := fun c => (algebraMap C _ c * T, 0, s * l c)
  let e2 : A → Localization.Away (X : C[X]) × A × Λ :=
    fun a => (0, a ^ (n a + 1), f a ^ (n a + 1))
  have hιP : ∀ a, ιE a ∈ P := fun a => by
    rw [hP]
    refine ⟨?_, fun _ _ => rfl⟩
    change ψD (algebraMap C _ (g a)) = _
    rw [hψDC, hψa]
    rfl
  have he1P : e1 ∈ P := by
    rw [hP]
    refine ⟨hψDT, fun a ha => ?_⟩
    change algebraMap Λ (Localization.Away (f a)) (f 0) = algebraMap Λ _ (s * u)
    rw [map_zero, map_zero, hzero a ha]
  have hβP : ∀ c ∈ tc, β c ∈ P := fun c hc => by
    rw [hP]
    refine ⟨?_, fun a ha => ?_⟩
    · change ψD (algebraMap C _ c * T) = algebraMap Λ (Localization.AtPrime q) (s * l c)
      rw [map_mul, hψDC, hψDT, map_mul, map_mul, hl c hc]
      ring
    · change algebraMap Λ (Localization.Away (f a)) (f 0) = algebraMap Λ _ (s * l c)
      rw [map_zero, map_zero, hzero a ha]
  have he2P : ∀ a ∈ t, e2 a ∈ P := fun a ha => by
    rw [hP]
    refine ⟨?_, fun b _ => ?_⟩
    · change ψD 0 = algebraMap Λ (Localization.AtPrime q) (f a ^ (n a + 1))
      rw [map_zero, hn a ha]
    · change algebraMap Λ (Localization.Away (f b)) (f (a ^ (n a + 1))) =
        algebraMap Λ _ (f a ^ (n a + 1))
      rw [map_pow]
  -- the finitely generated subalgebra `B`
  let G : Set (Localization.Away (X : C[X]) × A × Λ) := ({e1} ∪ β '' ↑tc) ∪ e2 '' ↑t
  obtain ⟨B, hBfg, hιB, he1B, hβB, he2B, hBP⟩ :
      ∃ B : Subalgebra R (Localization.Away (X : C[X]) × A × Λ), B.FG ∧ (∀ a, ιE a ∈ B) ∧
        e1 ∈ B ∧ (∀ c ∈ tc, β c ∈ B) ∧ (∀ a ∈ t, e2 a ∈ B) ∧ B ≤ P := by
    refine ⟨ιE.range ⊔ Algebra.adjoin R G, ?_, fun a => ?_, ?_, fun c hc => ?_, fun a ha => ?_, ?_⟩
    · refine Subalgebra.FG.sup ?_ (Subalgebra.fg_def.2 ⟨G, ?_, rfl⟩)
      · rw [← Algebra.map_top]
        exact (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG).map ιE
      · exact ((Set.finite_singleton e1).union (tc.finite_toSet.image β)).union
          (t.finite_toSet.image e2)
    · exact Algebra.mem_sup_left (AlgHom.mem_range_self ιE a)
    · exact Algebra.mem_sup_right (Algebra.subset_adjoin (Or.inl (Or.inl rfl)))
    · exact Algebra.mem_sup_right (Algebra.subset_adjoin (Or.inl (Or.inr ⟨c, hc, rfl⟩)))
    · exact Algebra.mem_sup_right (Algebra.subset_adjoin (Or.inr ⟨a, ha, rfl⟩))
    · refine sup_le ?_ (Algebra.adjoin_le ?_)
      · rintro _ ⟨a, rfl⟩
        exact hιP a
      · rintro x ((rfl | ⟨c, hc, rfl⟩) | ⟨a, ha, rfl⟩)
        · exact he1P
        · exact hβP c hc
        · exact he2P a ha
  have : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).1 hBfg
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  let gB : A →ₐ[R] B := ιE.codRestrict B hιB
  let hB : B →ₐ[R] Λ := (AlgHom.snd R A Λ).comp ((AlgHom.snd R _ (A × Λ)).comp B.val)
  have hcomp : hB.comp gB = f := by
    ext a
    rfl
  let e1' : B := ⟨e1, he1B⟩
  -- `B_{e1} ≅ D`, which is smooth
  have he1H : e1' ∈ singularIdeal R B := by
    let φ1 : B →ₐ[R] Localization.Away (X : C[X]) := (AlgHom.fst R _ (A × Λ)).comp B.val
    have hφ1 : φ1 e1' = T := rfl
    refine mem_singularIdeal_of_smooth e1' (smooth_away_of_isLocalization φ1 e1' ?_ ?_ ?_)
    · rw [hφ1]
      exact IsLocalization.Away.algebraMap_isUnit (X : C[X])
    · refine away_X_induction tc htc (fun y => ∃ (n : ℕ) (b : B), y * φ1 e1' ^ n = φ1 b)
        ?_ ?_ ?_ ?_ ?_ ?_
      · rintro x y ⟨n1, b1, h1⟩ ⟨n2, b2, h2⟩
        refine ⟨n1 + n2, b1 * e1' ^ n2 + b2 * e1' ^ n1, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h1, ← h2]
        ring
      · rintro x y ⟨n1, b1, h1⟩ ⟨n2, b2, h2⟩
        refine ⟨n1 + n2, b1 * b2, ?_⟩
        rw [map_mul, ← h1, ← h2]
        ring
      · intro r
        exact ⟨0, algebraMap R B r, by rw [pow_zero, mul_one, AlgHom.commutes]⟩
      · exact ⟨0, e1', by rw [pow_zero, mul_one]; exact hφ1.symm⟩
      · intro c hc
        exact ⟨1, ⟨β c, hβB c hc⟩, by rw [pow_one]; rfl⟩
      · rintro y m ⟨k, b, hb⟩
        refine ⟨m + k, b, ?_⟩
        rw [← hb, hφ1, pow_add]
        ring
    · intro b hb0
      refine ⟨1, ?_⟩
      have hbP := (hP _).1 (hBP b.2)
      have hd : (b : Localization.Away (X : C[X]) × A × Λ).1 = 0 := hb0
      have hl0 : s * (b : Localization.Away (X : C[X]) × A × Λ).2.2 = 0 := by
        apply hs
        rw [← hbP.1, hd, map_zero]
      apply Subtype.ext
      rw [pow_one, Subalgebra.coe_mul, Subalgebra.coe_zero]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · change T * (b : Localization.Away (X : C[X]) × A × Λ).1 = 0
        rw [hd, mul_zero]
      · change (0 : A) * _ = 0
        rw [zero_mul]
      · change s * u * (b : Localization.Away (X : C[X]) × A × Λ).2.2 = 0
        rw [mul_right_comm, hl0, zero_mul]
  -- `B_{e2 a} ≅ A_a`, which is smooth since `a ∈ H_{A/R}`
  have he2H : ∀ (a : A) (ha : a ∈ t), (⟨e2 a, he2B a ha⟩ : B) ∈ singularIdeal R B := by
    intro a ha
    have := smooth_away_of_mem_singularIdeal (htH a ha)
    let φ2 : B →ₐ[R] Localization.Away a :=
      (IsScalarTower.toAlgHom R A (Localization.Away a)).comp
        ((AlgHom.fst R A Λ).comp ((AlgHom.snd R _ (A × Λ)).comp B.val))
    have hφ2 : φ2 ⟨e2 a, he2B a ha⟩ = algebraMap A (Localization.Away a) a ^ (n a + 1) := by
      change algebraMap A (Localization.Away a) (a ^ (n a + 1)) = _
      rw [map_pow]
    have hφ2g : ∀ z : A, φ2 (gB z) = algebraMap A (Localization.Away a) z := fun z => rfl
    refine mem_singularIdeal_of_smooth _ (smooth_away_of_isLocalization φ2 _ ?_ ?_ ?_)
    · rw [hφ2]
      exact (IsLocalization.Away.algebraMap_isUnit a).pow _
    · intro y
      obtain ⟨m, a', hm⟩ := IsLocalization.Away.surj a y
      refine ⟨m, gB (a' * a ^ (n a * m)), ?_⟩
      rw [hφ2, hφ2g, map_mul, ← hm, map_pow]
      ring
    · intro b hb0
      have hbP := (hP _).1 (hBP b.2)
      obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq a
        (show algebraMap A (Localization.Away a) (b : Localization.Away (X : C[X]) × A × Λ).2.1 =
          algebraMap A (Localization.Away a) 0 by rw [map_zero]; exact hb0)
      rw [mul_zero] at hk
      obtain ⟨k', hk'⟩ := IsLocalization.Away.exists_of_eq (f a) (hbP.2 a ha)
      have hΛ : f a ^ (k + k') * (b : Localization.Away (X : C[X]) × A × Λ).2.2 = 0 := by
        have h1 : f (a ^ k * (b : Localization.Away (X : C[X]) × A × Λ).2.1) = 0 := by
          rw [hk, map_zero]
        rw [map_mul, map_pow] at h1
        calc f a ^ (k + k') * (b : Localization.Away (X : C[X]) × A × Λ).2.2
            = f a ^ k * (f a ^ k' * (b : Localization.Away (X : C[X]) × A × Λ).2.2) := by ring
          _ = f a ^ k * (f a ^ k' * f (b : Localization.Away (X : C[X]) × A × Λ).2.1) := by
            rw [hk']
          _ = f a ^ k' * (f a ^ k * f (b : Localization.Away (X : C[X]) × A × Λ).2.1) := by ring
          _ = 0 := by rw [h1, mul_zero]
      refine ⟨k + k' + 1, ?_⟩
      have hle : k + k' ≤ (n a + 1) * (k + k' + 1) := by nlinarith
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_zero]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · change (0 : Localization.Away (X : C[X])) ^ (k + k' + 1) * _ = 0
        rw [zero_pow (Nat.succ_ne_zero _), zero_mul]
      · change (a ^ (n a + 1)) ^ (k + k' + 1) * (b : Localization.Away (X : C[X]) × A × Λ).2.1 = 0
        rw [← pow_mul]
        exact pow_mul_eq_zero_of_le hk (le_trans (Nat.le_add_right k k') hle)
      · change (f a ^ (n a + 1)) ^ (k + k' + 1) *
          (b : Localization.Away (X : C[X]) × A × Λ).2.2 = 0
        rw [← pow_mul]
        exact pow_mul_eq_zero_of_le hΛ hle
  refine ⟨B, inferInstance, inferInstance, inferInstance, gB, hB, hcomp, ?_, ?_⟩
  · change ((singularIdeal R A).map f).radical ≤ ((singularIdeal R B).map hB).radical
    rw [Ideal.radical_le_radical_iff, ← ht', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨n a + 1, Ideal.mem_map_of_mem hB (he2H a ha)⟩
  · intro hle
    exact hμq (hle (Ideal.le_radical (Ideal.mem_map_of_mem hB he1H)))

end Langlands.CommutativeAlgebra.Popescu
