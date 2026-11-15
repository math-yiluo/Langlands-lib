import Langlands.CommutativeAlgebra.Popescu.CharPStep13
import Mathlib

/-! # The bottom case in the proof of Stacks Lemma 16.11.4 (07FJ)

Steps (19)–(26) of the proof of Stacks Lemma 16.11.4: over the quotient `R₁` of
`R = K[t₁, …, t_d]` by `(γ₁ᵉ, …, γ_dᵉ)`, the map `B → Λ₁ → (Λ₁)_Q` factors through a smooth algebra
over `(R₁)_{Q ∩ R₁}`. -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.CharP

open IsLocalRing MvPolynomial TensorProduct SmoothingAlgebra

/-- A prime `Q` of a quotient `Λ₁` of `Λ` lying over `q` is minimal when `Λ₁` kills
`(pᵢ δᵢ)ᵉ` with `δᵢ ∉ q` and `qⁿΛ_q ⊆ (pᵢᵉ)Λ_q`. -/
theorem minimal_of_pow_le {Λ Λ₁ : Type*} [CommRing Λ] [CommRing Λ₁] (q : Ideal Λ) [q.IsPrime]
    (τ : Λ →+* Λ₁) (hτ : Function.Surjective τ) {d : ℕ} (p δ : Fin d → Λ) (e n : ℕ)
    (hδ : ∀ i, δ i ∉ q) (hτ0 : ∀ i, τ (p i * δ i) ^ e = 0)
    (hqn : maximalIdeal (Localization.AtPrime q) ^ n ≤
      Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (p i ^ e)))
    (Q : Ideal Λ₁) [Q.IsPrime] (hQ : Q.comap τ = q) : Q ∈ minimalPrimes Λ₁ := by
  refine ⟨⟨inferInstance, bot_le⟩, fun Q' hQ' hQ'Q => ?_⟩
  have hQ'p : Q'.IsPrime := hQ'.1
  have hq'q : Q'.comap τ ≤ q := hQ ▸ Ideal.comap_mono hQ'Q
  have hp : ∀ i, p i ^ e ∈ Q'.comap τ := fun i => by
    have h1 : τ (p i) ^ e * τ (δ i) ^ e ∈ Q' := by
      rw [← mul_pow, ← map_mul, hτ0 i]; exact Q'.zero_mem
    have h2 : τ (δ i) ^ e ∉ Q' := fun h => hδ i (by
      rw [← hQ, Ideal.mem_comap]; exact hQ'Q (hQ'p.mem_of_pow_mem _ h))
    rw [Ideal.mem_comap, map_pow]
    exact (hQ'p.mem_or_mem h1).resolve_right h2
  have hdisj : Disjoint (q.primeCompl : Set Λ) (Q'.comap τ) :=
    Set.disjoint_left.mpr fun x hx hx' => hx (hq'q hx')
  have hPprime : ((Q'.comap τ).map (algebraMap Λ (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance hdisj
  have hspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (p i ^ e)) ≤
      (Q'.comap τ).map (algebraMap Λ (Localization.AtPrime q)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem _ (hp i)
  have hqq' : q ≤ Q'.comap τ := by
    intro x hx
    have hx' : algebraMap Λ (Localization.AtPrime q) x ∈ maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q x).mpr hx
    have h3 : algebraMap Λ (Localization.AtPrime q) x ∈
        (Q'.comap τ).map (algebraMap Λ (Localization.AtPrime q)) :=
      hPprime.mem_of_pow_mem n (hspan (hqn (Ideal.pow_mem_pow hx' n)))
    have h4 := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl
      (Localization.AtPrime q) (I := Q'.comap τ) inferInstance hdisj
    rw [← h4]
    exact h3
  intro x hx
  obtain ⟨y, rfl⟩ := hτ x
  have hy : y ∈ q := by rw [← hQ]; exact hx
  exact hqq' hy

section Bottom

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A]

/-- The generic core of steps (21)–(26) of Stacks 07FJ. Given an essentially smooth `P`-algebra
`D`, a map `ā : A → D`, compatible with `ι : k → P`, and elements `πᵢ ∈ P`, `wᵢⱼ ∈ D` with
`πᵢ^{2N} = Σⱼ wᵢⱼ ā(aⱼ)` in `D`, and given ring maps `κ : P → L`, `ℓ : L → M`, `μ : D → M` with
`ℓ ∘ κ = μ ∘ (P → D)` and elements `tᵢ ∈ L`, the smoothing algebra `B` maps to a smooth
`L`-algebra `T` with `xᵢ ↦ κ(πᵢ) tᵢ` and `zᵢⱼ ↦ tᵢ^{2N} zᵢⱼ`, together with `v : T → M`. -/
theorem exists_bottom_aux {P D L M : Type u} [CommRing P] [CommRing D] [CommRing L] [CommRing M]
    [Algebra P D] (hES : EssentiallySmooth P D) (ιk : k →+* P) {d r : ℕ} (N : ℕ)
    (a : Fin r → A) (πP : Fin d → P) (abar : A →+* D)
    (habark : ∀ c : k, abar (algebraMap k A c) = algebraMap P D (ιk c))
    (w : Fin d → Fin r → D)
    (hrelD : ∀ i, algebraMap P D (πP i) ^ (2 * N) = ∑ j, w i j * abar (a j))
    (κ : P →+* L) (ℓ : L →+* M) (μ : D →+* M) (hℓκ : ∀ y, ℓ (κ y) = μ (algebraMap P D y))
    (tL : Fin d → L) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra L T) (β : Alg d (2 * N) a →+* T) (v : T →+* M),
      Algebra.Smooth L T ∧
      (∀ i, β (mk d (2 * N) a (X (Sum.inl i))) = algebraMap L T (κ (πP i) * tL i)) ∧
      (∀ c : k, β (algebraMap k (Alg d (2 * N) a) c) = algebraMap L T (κ (ιk c))) ∧
      (∀ x, v (algebraMap L T x) = ℓ x) ∧
      (∀ x : A, v (β (algebraMap A _ x)) = μ (abar x)) ∧
      (∀ i j, v (β (mk d (2 * N) a (X (Sum.inr (i, j))))) = ℓ (tL i) ^ (2 * N) * μ (w i j)) := by
  classical
  -- `k[x]`-algebra structures
  letI : Algebra (MvPolynomial (Fin d) k) P := (eval₂Hom ιk πP).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) k) D :=
    ((algebraMap P D).comp (algebraMap (MvPolynomial (Fin d) k) P)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) P D := .of_algebraMap_eq fun _ => rfl
  have hXP : ∀ i, algebraMap (MvPolynomial (Fin d) k) P (X i) = πP i := fun i =>
    eval₂_X _ _ _
  have hCP : ∀ c : k, algebraMap (MvPolynomial (Fin d) k) P (C c) = ιk c := fun c =>
    eval₂_C _ _ _
  -- the map `B → D`
  let βD₀ : Alg d (2 * N) a →+* D := liftHom d (2 * N) a abar
    (fun i => algebraMap P D (πP i)) w hrelD
  have hβD₀A : ∀ x, βD₀ (algebraMap A _ x) = abar x := fun x => liftHom_algebraMap _ _ _ _ x
  have hβD₀X : ∀ i, βD₀ (mk d (2 * N) a (X (Sum.inl i))) = algebraMap P D (πP i) := fun i =>
    liftHom_X _ _ _ _ i
  have hβD₀Z : ∀ i j, βD₀ (mk d (2 * N) a (X (Sum.inr (i, j)))) = w i j := fun i j =>
    liftHom_Z _ _ _ _ i j
  have hβD₀ : βD₀.comp (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a)) =
      algebraMap (MvPolynomial (Fin d) k) D := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show βD₀ (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c)) =
        algebraMap P D (algebraMap (MvPolynomial (Fin d) k) P (C c))
      have e1 : algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c) =
          algebraMap A (Alg d (2 * N) a) (algebraMap k A c) :=
        (IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Alg d (2 * N) a) c).symm.trans
          (IsScalarTower.algebraMap_apply k A (Alg d (2 * N) a) c)
      rw [e1, hβD₀A, habark, hCP]
    · intro i
      show βD₀ (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (X i)) =
        algebraMap P D (algebraMap (MvPolynomial (Fin d) k) P (X i))
      rw [algebraMap_X, hβD₀X, hXP]
  let βD : Alg d (2 * N) a →ₐ[MvPolynomial (Fin d) k] D :=
    { βD₀ with commutes' := fun p => RingHom.congr_fun hβD₀ p }
  -- `B' = P ⊗[k[x]] B → D` and the smooth factorization
  let h : P ⊗[MvPolynomial (Fin d) k] Alg d (2 * N) a →ₐ[P] D :=
    Algebra.TensorProduct.lift (Algebra.ofId P D) βD fun _ _ => Commute.all _ _
  obtain ⟨T₀, _, _, hT₀sm, g₀, t₀, hgt⟩ :=
    hasSmoothFactorizations_of_essentiallySmooth hES
      (P ⊗[MvPolynomial (Fin d) k] Alg d (2 * N) a) h
  haveI := hT₀sm
  let iB : Alg d (2 * N) a →+* P ⊗[MvPolynomial (Fin d) k] Alg d (2 * N) a :=
    (Algebra.TensorProduct.includeRight :
      Alg d (2 * N) a →ₐ[MvPolynomial (Fin d) k] _).toRingHom
  have H1 : ∀ p : MvPolynomial (Fin d) k, iB (algebraMap _ (Alg d (2 * N) a) p) =
      algebraMap P _ (algebraMap _ P p) := fun p =>
    (Algebra.TensorProduct.algebraMap_apply' p).symm.trans
      (Algebra.TensorProduct.algebraMap_apply p)
  have htg : ∀ y, t₀ (g₀ (iB y)) = βD₀ y := fun y => by
    rw [← AlgHom.comp_apply, hgt]
    show h (1 ⊗ₜ y) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  -- `T = L ⊗[P] T₀`
  letI : Algebra P L := κ.toAlgebra
  let iT : T₀ →+* L ⊗[P] T₀ :=
    (Algebra.TensorProduct.includeRight : T₀ →ₐ[P] _).toRingHom
  let jT : L →+* L ⊗[P] T₀ := algebraMap L _
  have H2 : ∀ y : P, jT (κ y) = iT (algebraMap P T₀ y) :=
    fun y => (Algebra.TensorProduct.algebraMap_apply (R := P) (S := L) (A := L) (B := T₀)
      (algebraMap P L y)).symm.trans
      ((Algebra.TensorProduct.algebraMap_apply y).symm.trans
        (Algebra.TensorProduct.algebraMap_apply' y))
  have hxT : ∀ i, jT (κ (πP i)) = iT (g₀ (iB (mk d (2 * N) a (X (Sum.inl i))))) := fun i => by
    rw [← algebraMap_X d (2 * N) a k i, H1, g₀.commutes, ← H2, hXP]
  have hrelT : ∀ i, jT (κ (πP i) * tL i) ^ (2 * N) =
      ∑ j, jT (tL i) ^ (2 * N) * iT (g₀ (iB (mk d (2 * N) a (X (Sum.inr (i, j)))))) *
        (iT.comp (g₀.toRingHom.comp (iB.comp (algebraMap A (Alg d (2 * N) a))))) (a j) :=
    fun i => by
    rw [map_mul, mul_pow, hxT, ← map_pow iT, ← map_pow g₀, ← map_pow iB, rel_eq,
      map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = _ * iT (g₀ (iB (algebraMap A (Alg d (2 * N) a) (a j))))
    rw [map_mul, map_mul, map_mul]
    ring
  let β : Alg d (2 * N) a →+* L ⊗[P] T₀ :=
    liftHom d (2 * N) a (iT.comp (g₀.toRingHom.comp (iB.comp (algebraMap A (Alg d (2 * N) a)))))
      (fun i => jT (κ (πP i) * tL i))
      (fun i j => jT (tL i) ^ (2 * N) * iT (g₀ (iB (mk d (2 * N) a (X (Sum.inr (i, j))))))) hrelT
  have hβA : ∀ x, β (algebraMap A _ x) = iT (g₀ (iB (algebraMap A (Alg d (2 * N) a) x))) :=
    fun x => liftHom_algebraMap _ _ _ _ x
  have hβX : ∀ i, β (mk d (2 * N) a (X (Sum.inl i))) = jT (κ (πP i) * tL i) :=
    fun i => liftHom_X _ _ _ _ i
  have hβZ : ∀ i j, β (mk d (2 * N) a (X (Sum.inr (i, j)))) =
      jT (tL i) ^ (2 * N) * iT (g₀ (iB (mk d (2 * N) a (X (Sum.inr (i, j)))))) := fun i j =>
    liftHom_Z _ _ _ _ i j
  have hβk : ∀ c : k, β (algebraMap k (Alg d (2 * N) a) c) = jT (κ (ιk c)) := fun c => by
    have e1 : algebraMap k (Alg d (2 * N) a) c = algebraMap A _ (algebraMap k A c) :=
      IsScalarTower.algebraMap_apply k A (Alg d (2 * N) a) c
    have e2 : algebraMap k (Alg d (2 * N) a) c =
        algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c) :=
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Alg d (2 * N) a) c
    rw [e1, hβA, ← e1, e2, H1, g₀.commutes, ← H2, hCP]
  -- the map `v : T → M`
  letI : Algebra P M := (μ.comp (algebraMap P D)).toAlgebra
  let ℓA : L →ₐ[P] M := { ℓ with commutes' := hℓκ }
  let t₀' : T₀ →ₐ[P] M :=
    { μ.comp t₀.toRingHom with
      commutes' := fun y => by
        show μ (t₀ (algebraMap _ T₀ y)) = μ (algebraMap P D y)
        rw [t₀.commutes] }
  let vA : L ⊗[P] T₀ →ₐ[P] M := Algebra.TensorProduct.lift ℓA t₀' fun _ _ => Commute.all _ _
  have hvj : ∀ x, vA (jT x) = ℓ x := fun x => by
    show vA (x ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hvi : ∀ z, vA (iT z) = μ (t₀ z) := fun z => by
    show vA (1 ⊗ₜ z) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  refine ⟨L ⊗[P] T₀, inferInstance, inferInstance, β, vA.toRingHom,
    inferInstance, hβX, hβk, hvj, fun x => ?_, fun i j => ?_⟩
  · show vA (β (algebraMap A _ x)) = _
    rw [hβA, hvi, htg, hβD₀A]
  · show vA (β _) = _
    rw [hβZ, map_mul, map_pow, hvj, hvi, htg, hβD₀Z]

variable {K Λ D R₁ Λ₁ : Type u} [CommRing K] [Algebra k K] [CommRing Λ]
  [Algebra k Λ] [CommRing D] [IsLocalRing D] [CommRing R₁] [CommRing Λ₁] [Algebra R₁ Λ₁]

/-- Steps (19)–(26) of Stacks 07FJ. Data: `φ : K → Λ` with `𝔭 = φ⁻¹(q)`, the factorization
`K_𝔭/𝔭ⁿ → D → Λ_q/qⁿΛ_q` from Lemma 16.11.2, elements `πᵢ ∈ K`, `δᵢ ∈ Λ ∖ q` with
`(δᵢ φ(πᵢ))^{2N} = Σⱼ λᵢⱼ f(aⱼ)` and `λᵢⱼ ≡ δᵢ^{2N} ψ(wᵢⱼ)` mod `qⁿΛ_q`, and maps
`σK : K → R₁`, `tᵢ ∈ R₁`, `τ : Λ → Λ₁` killing `(πᵢ tᵢ)ᵉ`. Then the map
`B = A[x, z]/(xᵢ^{2N} - Σⱼ zᵢⱼ aⱼ) → Λ₁ → (Λ₁)_Q` (with `xᵢ ↦ δᵢ φ(πᵢ)`, `zᵢⱼ ↦ λᵢⱼ`) factors
through a smooth algebra `T` over `(R₁)_{Q ∩ R₁}` with `xᵢ ↦ πᵢ tᵢ`. -/
theorem exists_bottom (φ : K →ₐ[k] Λ) (q : Ideal Λ) [q.IsPrime] (𝔭 : Ideal K) [𝔭.IsPrime]
    (h𝔭 : 𝔭 = q.comap (φ : K →+* Λ)) {n : ℕ} (hn : 0 < n)
    [Algebra (localTruncation 𝔭 n) D] (ψ : D →+* localTruncation q n) [IsLocalHom ψ]
    (hψ : ψ.Flat) (hES : EssentiallySmooth (localTruncation 𝔭 n) D)
    (hψφ : ∀ y : K, ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
      toLocalTruncation q n (φ y))
    (f : A →ₐ[k] Λ) (hf : ∀ x : A, ∃ b, ψ b = toLocalTruncation q n (f x))
    {d r : ℕ} (N : ℕ) (a : Fin r → A) (π : Fin d → K) (δ : Fin d → Λ) (hδ : ∀ i, δ i ∉ q)
    (lam : Fin d → Fin r → Λ) (w : Fin d → Fin r → D)
    (hlam : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, lam i j * f (a j))
    (hw : ∀ i j, toLocalTruncation q n (lam i j) =
      toLocalTruncation q n (δ i) ^ (2 * N) * ψ (w i j))
    (e : ℕ)
    (h𝔭n : maximalIdeal (Localization.AtPrime 𝔭) ^ n ≤
      Ideal.span (Set.range fun i => algebraMap K (Localization.AtPrime 𝔭) (π i ^ e)))
    (hqn : maximalIdeal (Localization.AtPrime q) ^ n ≤
      Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (φ (π i) ^ e)))
    (σK : K →+* R₁) (t : Fin d → R₁) (τ : Λ →+* Λ₁)
    (hστ : ∀ y, algebraMap R₁ Λ₁ (σK y) = τ (φ y)) (htτ : ∀ i, algebraMap R₁ Λ₁ (t i) = τ (δ i))
    (hσ0 : ∀ i, (σK (π i) * t i) ^ e = 0)
    (Q : Ideal Λ₁) [Q.IsPrime] (hQ : Q.comap τ = q) :
    ∃ (T : Type u) (_ : CommRing T)
      (_ : Algebra (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T)
      (β : Alg d (2 * N) a →+* T) (v : T →+* Localization.AtPrime Q),
      Algebra.Smooth (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T ∧
      (∀ i, β (mk d (2 * N) a (X (Sum.inl i))) =
        algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T
          (algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) (σK (π i) * t i))) ∧
      (∀ c : k, β (algebraMap k (Alg d (2 * N) a) c) =
        algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T
          (algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))
            (σK (algebraMap k K c)))) ∧
      (∀ x, v (algebraMap _ T x) =
        Localization.localRingHom (Q.comap (algebraMap R₁ Λ₁)) Q (algebraMap R₁ Λ₁) rfl x) ∧
      (∀ x : A, v (β (algebraMap A _ x)) = algebraMap Λ₁ _ (τ (f x))) ∧
      (∀ i, v (β (mk d (2 * N) a (X (Sum.inl i)))) =
        algebraMap Λ₁ _ (τ (φ (π i) * δ i))) ∧
      (∀ i j, v (β (mk d (2 * N) a (X (Sum.inr (i, j))))) = algebraMap Λ₁ _ (τ (lam i j))) := by
  classical
  haveI : IsLocalRing (localTruncation q n) := isLocalRing_localTruncation q hn
  have hψinj : Function.Injective ψ := SmoothApprox.injective_of_flat_of_isLocalHom ψ hψ
  -- units
  have hunitΛ : ∀ x : Λ, x ∉ q → IsUnit (algebraMap Λ₁ (Localization.AtPrime Q) (τ x)) :=
    fun x hx => IsLocalization.map_units (Localization.AtPrime Q)
      (⟨τ x, fun h => hx (by rw [← hQ]; exact h)⟩ : Q.primeCompl)
  have hunitR : ∀ y : R₁, algebraMap R₁ Λ₁ y ∉ Q →
      IsUnit (algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) y) :=
    fun y hy => IsLocalization.map_units _
      (⟨y, hy⟩ : (Q.comap (algebraMap R₁ Λ₁)).primeCompl)
  have htunit : ∀ i, IsUnit (algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))
      (t i)) := fun i => hunitR _ (by
    rw [htτ]; intro h; exact hδ i (by rw [← hQ]; exact h))
  have hδunit : ∀ i, IsUnit (toLocalTruncation q n (δ i)) := fun i =>
    (IsLocalization.map_units (Localization.AtPrime q) (⟨δ i, hδ i⟩ : q.primeCompl)).map
      (Ideal.Quotient.mk _)
  -- the map `κ : K_𝔭/𝔭ⁿ → (R₁)_𝔯`
  let L₁ := Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))
  let κ₀ : K →+* L₁ := (algebraMap R₁ L₁).comp σK
  have hmem : ∀ y : K, φ y ∈ q → y ∈ 𝔭 := fun y h => by rw [h𝔭]; exact h
  have hκ₀ : ∀ y : 𝔭.primeCompl, IsUnit (κ₀ y) := fun y => by
    refine hunitR (σK y) ?_
    rw [hστ]; intro h
    exact y.2 (hmem _ (by rw [← hQ, Ideal.mem_comap]; exact h))
  let κ₁ : Localization.AtPrime 𝔭 →+* L₁ := IsLocalization.lift (M := 𝔭.primeCompl) hκ₀
  have hκ₁ : ∀ y, κ₁ (algebraMap K _ y) = κ₀ y := IsLocalization.lift_eq hκ₀
  have hκker : maximalIdeal (Localization.AtPrime 𝔭) ^ n ≤ RingHom.ker κ₁ := by
    refine h𝔭n.trans ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hκ₁, map_pow]
    have h0 : algebraMap R₁ L₁ ((σK (π i) * t i) ^ e) = 0 := by rw [hσ0, map_zero]
    rw [map_pow, map_mul, mul_pow] at h0
    exact ((htunit i).pow e).mul_left_eq_zero.mp h0
  let κ : localTruncation 𝔭 n →+* L₁ := Ideal.Quotient.lift _ κ₁ fun x hx => hκker hx
  have hκ : ∀ y : K, κ (toLocalTruncation 𝔭 n y) = algebraMap R₁ L₁ (σK y) := fun y =>
    hκ₁ y
  -- the map `ρ : Λ_q/qⁿΛ_q → (Λ₁)_Q`
  let ρ₀ : Λ →+* Localization.AtPrime Q := (algebraMap Λ₁ _).comp τ
  have hρ₀ : ∀ x : q.primeCompl, IsUnit (ρ₀ x) := fun x => hunitΛ x x.2
  let ρ₁ : Localization.AtPrime q →+* Localization.AtPrime Q :=
    IsLocalization.lift (M := q.primeCompl) hρ₀
  have hρ₁ : ∀ x, ρ₁ (algebraMap Λ _ x) = ρ₀ x := IsLocalization.lift_eq hρ₀
  have hρker : maximalIdeal (Localization.AtPrime q) ^ n ≤ RingHom.ker ρ₁ := by
    refine hqn.trans ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hρ₁]
    have h0 : τ (φ (π i) * δ i) ^ e = 0 := by
      rw [map_mul, ← hστ, ← htτ, ← map_mul, ← map_pow, hσ0 i, map_zero]
    have h1 := congrArg (algebraMap Λ₁ (Localization.AtPrime Q)) h0
    rw [map_pow, map_mul, map_mul, mul_pow, map_zero] at h1
    show algebraMap Λ₁ _ (τ (φ (π i) ^ e)) = 0
    rw [map_pow, map_pow]
    exact ((hunitΛ _ (hδ i)).pow e).mul_left_eq_zero.mp h1
  let ρ : localTruncation q n →+* Localization.AtPrime Q :=
    Ideal.Quotient.lift _ ρ₁ fun x hx => hρker hx
  have hρ : ∀ x : Λ, ρ (toLocalTruncation q n x) = algebraMap Λ₁ _ (τ x) := fun x => hρ₁ x
  -- the map `ā : A → D`
  have hrange : ∀ x : A, ((toLocalTruncation q n).comp f.toRingHom) x ∈ ψ.range := fun x => by
    obtain ⟨b, hb⟩ := hf x
    exact ⟨b, hb⟩
  let eψ : D ≃+* ψ.range := RingEquiv.ofBijective ψ.rangeRestrict
    ⟨fun x y h => hψinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩
  let abar : A →+* D := eψ.symm.toRingHom.comp
    (((toLocalTruncation q n).comp f.toRingHom).codRestrict ψ.range hrange)
  have habar : ∀ x, ψ (abar x) = toLocalTruncation q n (f x) := fun x =>
    congrArg Subtype.val (eψ.apply_symm_apply ⟨_, hrange x⟩)
  have habark : ∀ c : k, abar (algebraMap k A c) = algebraMap (localTruncation 𝔭 n) D
      (((toLocalTruncation 𝔭 n).comp (algebraMap k K)) c) := fun c => by
    apply hψinj
    rw [habar, AlgHom.commutes, RingHom.comp_apply, hψφ, AlgHom.commutes]
  have hrelD : ∀ i, algebraMap _ D (toLocalTruncation 𝔭 n (π i)) ^ (2 * N) =
      ∑ j, w i j * abar (a j) := fun i => by
    apply hψinj
    apply ((hδunit i).pow (2 * N)).mul_left_cancel
    calc toLocalTruncation q n (δ i) ^ (2 * N) *
          ψ (algebraMap _ D (toLocalTruncation 𝔭 n (π i)) ^ (2 * N))
        = toLocalTruncation q n ((δ i * φ (π i)) ^ (2 * N)) := by
          rw [map_pow ψ, hψφ, map_pow, map_mul, mul_pow]
      _ = ∑ j, toLocalTruncation q n (lam i j) * toLocalTruncation q n (f (a j)) := by
          rw [hlam, map_sum]
          simp only [map_mul]
      _ = toLocalTruncation q n (δ i) ^ (2 * N) * ψ (∑ j, w i j * abar (a j)) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hw, map_mul, habar]
          ring
  -- `ℓ ∘ κ = ρ ∘ ψ ∘ (P → D)`
  let ℓ₀ : L₁ →+* Localization.AtPrime Q :=
    Localization.localRingHom (Q.comap (algebraMap R₁ Λ₁)) Q (algebraMap R₁ Λ₁) rfl
  have hℓκ : ℓ₀.comp κ = (ρ.comp ψ).comp (algebraMap (localTruncation 𝔭 n) D) := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext 𝔭.primeCompl
    ext y
    show ℓ₀ (κ (toLocalTruncation 𝔭 n y)) =
      ρ (ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)))
    rw [hκ, hψφ, hρ, Localization.localRingHom_to_map, hστ]
  obtain ⟨T, _, _, β, v, hTsm, hβX, hβk, hvj, hvA, hvZ⟩ :=
    exists_bottom_aux hES ((toLocalTruncation 𝔭 n).comp (algebraMap k K)) N a
      (fun i => toLocalTruncation 𝔭 n (π i)) abar habark w hrelD κ ℓ₀ (ρ.comp ψ)
      (fun y => RingHom.congr_fun hℓκ y) (fun i => algebraMap R₁ L₁ (t i))
  refine ⟨T, inferInstance, inferInstance, β, v, hTsm, fun i => ?_, fun c => ?_, hvj,
    fun x => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [hβX, hκ]
    simp only [map_mul]
    rfl
  · rw [hβk, RingHom.comp_apply, hκ]
  · rw [hvA, RingHom.comp_apply, habar, hρ]
  · rw [hβX, hvj, hκ, ← map_mul, Localization.localRingHom_to_map]
    simp only [map_mul, hστ, htτ]
  · rw [hvZ, Localization.localRingHom_to_map, htτ, RingHom.comp_apply, ← hρ, ← map_pow, ← map_mul,
      ← hw, hρ]

end Bottom

end Langlands.CommutativeAlgebra.Popescu.CharP
