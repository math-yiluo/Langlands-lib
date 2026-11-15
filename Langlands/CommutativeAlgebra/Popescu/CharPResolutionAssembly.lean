import Langlands.CommutativeAlgebra.Popescu.CharPResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionAssembly
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardSmoothStatement
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardRetractStatement
import Langlands.CommutativeAlgebra.Popescu.SequenceDimZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothApproximationStatement
import Langlands.CommutativeAlgebra.Popescu.CharPParameters
import Langlands.CommutativeAlgebra.Popescu.CharPBottom
import Langlands.CommutativeAlgebra.Popescu.LocalLifting
import Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_mvPolynomial
import Mathlib

/-! # Assembly of Stacks Lemma 16.11.4 (07FJ): resolution in positive characteristic -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.CharP

open IsLocalRing MvPolynomial TensorProduct SmoothingAlgebra

section Bottom

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A]

/-- The bottom hypothesis of `SequenceDimZeroResolutionStatement` in the proof of Stacks 07FJ:
`R = K[t₁, …, t_d]` is a `k[x₁, …, x_d]`-algebra via `xᵢ ↦ γᵢ = πᵢ tᵢ`, `Λ` an `R`-algebra via
`tᵢ ↦ δᵢ`, `A' = R ⊗_{k[x]} C` with `C` a retract-enlargement of the smoothing algebra `B`, and
`f' : A' → Λ` induced by `B → Λ`. For quotients `σ : R → R₁`, `τ : Λ → Λ₁` killing `γᵢᵉ` and a
prime `Q` over `q`, `Q` is minimal and `A' → (Λ₁)_Q` factors through a smooth
`(R₁)_{Q ∩ R₁}`-algebra. -/
theorem bottom_condition {K Λ D Cr : Type u} [CommRing K] [Algebra k K] [CommRing Λ]
    [Algebra k Λ] [CommRing D] [IsLocalRing D] [CommRing Cr]
    (φ : K →ₐ[k] Λ) (q : Ideal Λ) [q.IsPrime] (𝔭 : Ideal K) [𝔭.IsPrime]
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
    [Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K)]
    (hγ : ∀ i, algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) (X i) =
      C (π i) * X i)
    (hγk : ∀ c : k, algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) (C c) =
      C (algebraMap k K c))
    [Algebra (MvPolynomial (Fin d) K) Λ]
    (hRΛ : ∀ x, algebraMap (MvPolynomial (Fin d) K) Λ x = eval₂Hom (φ : K →+* Λ) δ x)
    [Algebra (MvPolynomial (Fin d) k) Λ]
    [IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) Λ]
    [Algebra (MvPolynomial (Fin d) k) Cr] (rC : Cr →ₐ[MvPolynomial (Fin d) k] Alg d (2 * N) a)
    (fB : Alg d (2 * N) a →ₐ[MvPolynomial (Fin d) k] Λ)
    (hfBA : ∀ x, fB (algebraMap A _ x) = f x)
    (hfBX : ∀ i, fB (mk d (2 * N) a (X (Sum.inl i))) = φ (π i) * δ i)
    (hfBZ : ∀ i j, fB (mk d (2 * N) a (X (Sum.inr (i, j)))) = lam i j)
    (R₁ Λ₁ : Type u) [CommRing R₁] [CommRing Λ₁] [Algebra R₁ Λ₁]
    (σ : MvPolynomial (Fin d) K →+* R₁) (τ : Λ →+* Λ₁) (hτ : Function.Surjective τ)
    (hσ0 : ∀ i, σ ((C (π i) * X i) ^ e) = 0)
    (hστ : ∀ x, τ (algebraMap (MvPolynomial (Fin d) K) Λ x) = algebraMap R₁ Λ₁ (σ x))
    (Q : Ideal Λ₁) [Q.IsPrime] (hQ : Q.comap τ = q) :
    Q ∈ minimalPrimes Λ₁ ∧
      ∃ (T : Type u) (_ : CommRing T)
        (_ : Algebra (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T)
        (u : MvPolynomial (Fin d) K ⊗[MvPolynomial (Fin d) k] Cr →+* T)
        (v : T →+* Localization.AtPrime Q),
        Algebra.Smooth (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T ∧
        u.comp (algebraMap (MvPolynomial (Fin d) K) _) =
          (algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T).comp
            ((algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))).comp σ) ∧
        v.comp u = (algebraMap Λ₁ (Localization.AtPrime Q)).comp
          (τ.comp (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial (Fin d) K) Λ)
            (fB.comp rC) (fun _ _ => Commute.all _ _)).toRingHom) := by
  classical
  have hστK : ∀ y, algebraMap R₁ Λ₁ ((σ.comp C) y) = τ (φ y) := fun y => by
    rw [RingHom.comp_apply, ← hστ, hRΛ, eval₂Hom_C]
    try rfl
  have htτ : ∀ i, algebraMap R₁ Λ₁ (σ (X i)) = τ (δ i) := fun i => by
    rw [← hστ, hRΛ, eval₂Hom_X']
  have hσ0' : ∀ i, ((σ.comp C) (π i) * σ (X i)) ^ e = 0 := fun i => by
    rw [RingHom.comp_apply, ← map_mul, ← map_pow]
    exact hσ0 i
  have hτ0 : ∀ i, τ (φ (π i) * δ i) ^ e = 0 := fun i => by
    have h1 : (φ (π i) * δ i) ^ e = algebraMap (MvPolynomial (Fin d) K) Λ ((C (π i) * X i) ^ e) := by
      rw [hRΛ, map_pow, map_mul, eval₂Hom_C, eval₂Hom_X']
      try rfl
    rw [← map_pow, h1, hστ, hσ0, map_zero]
  have hQmin := minimal_of_pow_le q τ hτ (fun i => φ (π i)) δ e n hδ hτ0 hqn Q hQ
  obtain ⟨T, _, _, β, v, hTsm, hβX, hβk, hvj, hvA, hvX, hvZ⟩ :=
    exists_bottom φ q 𝔭 h𝔭 hn ψ hψ hES hψφ f hf N a π δ hδ lam w hlam hw e h𝔭n hqn
      (σ.comp C) (fun i => σ (X i)) τ hστK htτ hσ0' Q hQ
  simp only [RingHom.comp_apply] at hβX hβk
  refine ⟨hQmin, T, inferInstance, inferInstance, ?_⟩
  let uR : MvPolynomial (Fin d) K →+* T :=
    (algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T).comp
      ((algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))).comp σ)
  let : Algebra (MvPolynomial (Fin d) K) T := uR.toAlgebra
  let : Algebra (MvPolynomial (Fin d) k) T :=
    (uR.comp (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) K) T :=
    .of_algebraMap_eq fun _ => rfl
  have hβ : β.comp (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a)) =
      algebraMap (MvPolynomial (Fin d) k) T := by
    apply MvPolynomial.ringHom_ext
    · intro c'
      have e1 : algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c') =
          algebraMap k (Alg d (2 * N) a) c' :=
        (IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Alg d (2 * N) a) c').symm
      show β (algebraMap _ (Alg d (2 * N) a) (C c')) =
        uR (algebraMap _ (MvPolynomial (Fin d) K) (C c'))
      rw [e1, hβk, hγk]
      try rfl
    · intro i
      show β (algebraMap _ (Alg d (2 * N) a) (X i)) =
        uR (algebraMap _ (MvPolynomial (Fin d) K) (X i))
      rw [algebraMap_X, hβX, hγ]
      show algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T
          (algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))
            (σ (C (π i)) * σ (X i))) =
        algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T
          (algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))
            (σ (C (π i) * X i)))
      rw [map_mul σ]
  let βB : Alg d (2 * N) a →ₐ[MvPolynomial (Fin d) k] T :=
    { β with commutes' := fun p => RingHom.congr_fun hβ p }
  let u' : MvPolynomial (Fin d) K ⊗[MvPolynomial (Fin d) k] Cr →ₐ[MvPolynomial (Fin d) K] T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ T) (βB.comp rC) fun _ _ => Commute.all _ _
  have hvβ : ∀ b, v (β b) = algebraMap Λ₁ (Localization.AtPrime Q) (τ (fB b)) := by
    have h : v.comp β = (algebraMap Λ₁ (Localization.AtPrime Q)).comp (τ.comp fB.toRingHom) := by
      apply ringHom_ext
      · intro x
        show v (β _) = algebraMap Λ₁ _ (τ (fB _))
        rw [hvA, hfBA]
      · intro i
        show v (β _) = algebraMap Λ₁ _ (τ (fB _))
        rw [hvX, hfBX]
      · intro i j
        show v (β _) = algebraMap Λ₁ _ (τ (fB _))
        rw [hvZ, hfBZ]
    exact fun b => RingHom.congr_fun h b
  refine ⟨u'.toRingHom, v, hTsm, RingHom.ext fun x => u'.commutes x, ?_⟩
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r c' =>
    have e1 : u' (r ⊗ₜ c') = uR r * β (rC c') :=
      (Algebra.TensorProduct.lift_tmul _ _ _ r c').trans rfl
    have e2 : (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial (Fin d) K) Λ)
        (fB.comp rC) (fun _ _ => Commute.all _ _)) (r ⊗ₜ c') =
        algebraMap (MvPolynomial (Fin d) K) Λ r * fB (rC c') :=
      (Algebra.TensorProduct.lift_tmul _ _ _ r c').trans rfl
    have e3 : v (uR r) = algebraMap Λ₁ (Localization.AtPrime Q)
        (τ (algebraMap (MvPolynomial (Fin d) K) Λ r)) := by
      show v (algebraMap _ T (algebraMap R₁ _ (σ r))) = _
      rw [hvj, Localization.localRingHom_to_map, hστ]
    show v (u' (r ⊗ₜ c')) = algebraMap Λ₁ (Localization.AtPrime Q)
      (τ ((Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial (Fin d) K) Λ)
        (fB.comp rC) (fun _ _ => Commute.all _ _)) (r ⊗ₜ c')))
    rw [e1, e2, map_mul, map_mul, map_mul, e3, hvβ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Bottom

section Main

/-- Steps 7–9 of the proof of Stacks 07FJ: from the parameters `πᵢ` of `K_𝔭`, the units `δᵢ`
of step (13) and the retract `C` of the smoothing algebra `B`, Lemmas 9.2 and 9.4 over
`R = K[t₁, …, t_d]` resolve `f` at `q`. -/
theorem resolution_of_parameters (n0 : StrictlyStandardSmoothStatement.{u})
    (hSDZ : SequenceDimZeroResolutionStatement.{u})
    {k A Λ K D Cr : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A]
    [CommRing Λ] [IsNoetherianRing Λ] [Algebra k Λ] [CommRing K] [Algebra k K] [IsNoetherianRing K]
    [Algebra.FinitePresentation k K] [Algebra.Smooth k K] [CommRing D] [IsLocalRing D]
    [CommRing Cr]
    (φ : K →ₐ[k] Λ) (q : Ideal Λ) [q.IsPrime] (𝔭 : Ideal K) [𝔭.IsPrime]
    (h𝔭 : 𝔭 = q.comap (φ : K →+* Λ)) {n : ℕ} (hn : 0 < n)
    [Algebra (localTruncation 𝔭 n) D] (ψ : D →+* localTruncation q n) [IsLocalHom ψ]
    (hψ : ψ.Flat) (hES : EssentiallySmooth (localTruncation 𝔭 n) D)
    (hψφ : ∀ y : K, ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
      toLocalTruncation q n (φ y))
    (f : A →ₐ[k] Λ) (hf : ∀ x : A, ∃ b, ψ b = toLocalTruncation q n (f x))
    {d r : ℕ} (N : ℕ) (a : Fin r → A) (ha' : Ideal.span (Set.range a) = singularIdeal k A)
    (π : Fin d → K) (δ : Fin d → Λ) (hδq : ∀ i, δ i ∉ q)
    (lam : Fin d → Fin r → Λ) (w : Fin d → Fin r → D)
    (hlam : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, lam i j * f (a j))
    (hw : ∀ i j, toLocalTruncation q n (lam i j) =
      toLocalTruncation q n (δ i) ^ (2 * N) * ψ (w i j))
    (e c : ℕ) (hc : 0 < c) (hedef : e = c * 8)
    (h𝔭n : maximalIdeal (Localization.AtPrime 𝔭) ^ n ≤
      Ideal.span (Set.range fun i => algebraMap K (Localization.AtPrime 𝔭) (π i ^ e)))
    (hqn : maximalIdeal (Localization.AtPrime q) ^ n ≤
      Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (φ (π i) ^ e)))
    (hpq : ∀ i, φ (π i) ∈ q)
    (h12' : ∀ (i : Fin d) (x : MvPolynomial (Fin d) K),
      (C (π i) * X i) ^ 2 * x ∈ Ideal.span ((fun j => (C (π j) * X j) ^ e) '' {j | j < i}) →
      C (π i) * X i * x ∈ Ideal.span ((fun j => (C (π j) * X j) ^ e) '' {j | j < i}))
    (h13' : ∀ (i : Fin d) (z : Λ), (δ i * φ (π i)) ^ 2 * z ∈
      Ideal.span ((fun j => (δ j * φ (π j)) ^ e) '' {j | j < i}) →
      δ i * φ (π i) * z ∈ Ideal.span ((fun j => (δ j * φ (π j)) ^ e) '' {j | j < i}))
    [Algebra (MvPolynomial (Fin d) k) Cr]
    [Algebra.FinitePresentation (MvPolynomial (Fin d) k) Cr]
    (gC : Alg d (2 * N) a →ₐ[MvPolynomial (Fin d) k] Cr)
    (rC : Cr →ₐ[MvPolynomial (Fin d) k] Alg d (2 * N) a)
    (hrg : rC.comp gC = AlgHom.id (MvPolynomial (Fin d) k) (Alg d (2 * N) a))
    (hss : ∀ b : Alg d (2 * N) a, Algebra.Smooth (MvPolynomial (Fin d) k) (Localization.Away b) →
      ∃ c, IsStrictlyStandard (MvPolynomial (Fin d) k) (gC b ^ c))
    (hssC : ∀ i, IsStrictlyStandard (MvPolynomial (Fin d) k)
      (algebraMap (MvPolynomial (Fin d) k) Cr (X i ^ c)))
    (hBa : ∀ j, algebraMap A (Alg d (2 * N) a) (a j) ∈
      singularIdeal (MvPolynomial (Fin d) k) (Alg d (2 * N) a)) :
    CanBeResolved k f q := by
  classical
  have : Algebra.Smooth K (MvPolynomial (Fin d) K) := {}
  -- Step 7: `R = K[t₁, …, t_d]` over `k[x₁, …, x_d]` (`xᵢ ↦ πᵢtᵢ`), `R → Λ` (`tᵢ ↦ δᵢ`)
  -- and `B → Λ`
  let iR : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) (K)) :=
    (aeval fun i => C (π i) * X i : MvPolynomial (Fin d) k →ₐ[k]
      MvPolynomial (Fin d) (K)).toRingHom.toAlgebra
  have hγ : ∀ i, algebraMap (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (K)) (X i) = C (π i) * X i :=
    fun i => aeval_X _ i
  have hγk : ∀ c' : k, algebraMap (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (K)) (C c') =
      C (algebraMap k (K) c') :=
    fun c' => (aeval_C _ c').trans rfl
  let iRΛ : Algebra (MvPolynomial (Fin d) (K)) Λ :=
    (eval₂Hom (φ : K →+* Λ) δ).toAlgebra
  let ixΛ : Algebra (MvPolynomial (Fin d) k) Λ :=
    ((algebraMap (MvPolynomial (Fin d) (K)) Λ).comp
      (algebraMap (MvPolynomial (Fin d) k)
        (MvPolynomial (Fin d) (K)))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (K)) Λ :=
    .of_algebraMap_eq fun _ => rfl
  have hγΛ : ∀ i, algebraMap (MvPolynomial (Fin d) (K)) Λ
      (C (π i) * X i) = δ i * φ (π i) := fun i => by
    show eval₂Hom (φ : K →+* Λ) δ (C (π i) * X i) = _
    rw [map_mul, eval₂Hom_C, eval₂Hom_X', mul_comm]
    try rfl
  have hrelΛ : ∀ i, (φ (π i) * δ i) ^ (2 * N) = ∑ j, lam i j * f.toRingHom (a j) := fun i => by
    rw [mul_comm]; exact hlam i
  let fB₀ : Alg d (2 * N) a →+* Λ :=
    liftHom d (2 * N) a f.toRingHom (fun i => φ (π i) * δ i) lam hrelΛ
  have hfB₀ : fB₀.comp (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a)) =
      algebraMap (MvPolynomial (Fin d) k) Λ := by
    apply MvPolynomial.ringHom_ext
    · intro c'
      have e1 : algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c') =
          algebraMap A (Alg d (2 * N) a) (algebraMap k A c') :=
        (IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Alg d (2 * N) a) c').symm.trans
          (IsScalarTower.algebraMap_apply k A (Alg d (2 * N) a) c')
      show fB₀ (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c')) =
        eval₂Hom (φ : K →+* Λ) δ
          (algebraMap (MvPolynomial (Fin d) k)
            (MvPolynomial (Fin d) (K)) (C c'))
      rw [e1, hγk, eval₂Hom_C]
      exact (liftHom_algebraMap f.toRingHom (fun i => φ (π i) * δ i) lam hrelΛ _).trans ((f.commutes c').trans (φ.commutes c').symm)
    · intro i
      show fB₀ (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (X i)) =
        eval₂Hom (φ : K →+* Λ) δ
          (algebraMap (MvPolynomial (Fin d) k)
            (MvPolynomial (Fin d) (K)) (X i))
      rw [SmoothingAlgebra.algebraMap_X, hγ, map_mul, eval₂Hom_C, eval₂Hom_X']
      exact liftHom_X f.toRingHom (fun i => φ (π i) * δ i) lam hrelΛ i
  let fB : Alg d (2 * N) a →ₐ[MvPolynomial (Fin d) k] Λ :=
    { fB₀ with commutes' := fun x => RingHom.congr_fun hfB₀ x }
  have hfBA : ∀ x, fB (algebraMap A (Alg d (2 * N) a) x) = f x := fun x =>
    liftHom_algebraMap f.toRingHom (fun i => φ (π i) * δ i) lam hrelΛ x
  have hfBX : ∀ i, fB (mk d (2 * N) a (X (Sum.inl i))) = φ (π i) * δ i := fun i =>
    liftHom_X f.toRingHom (fun i => φ (π i) * δ i) lam hrelΛ i
  have hfBZ : ∀ i j, fB (mk d (2 * N) a (X (Sum.inr (i, j)))) = lam i j := fun i j =>
    liftHom_Z f.toRingHom (fun i => φ (π i) * δ i) lam hrelΛ i j
  -- Step 8: Lemmas 9.2 and 9.4 over `R`, for `A' = R ⊗_{k[x]} C → Λ`
  let f' : MvPolynomial (Fin d) (K) ⊗[MvPolynomial (Fin d) k] Cr →ₐ[
      MvPolynomial (Fin d) (K)] Λ :=
    Algebra.TensorProduct.lift (Algebra.ofId _ Λ) (fB.comp rC) (fun _ _ => Commute.all _ _)
  have hA'C : ∀ x : MvPolynomial (Fin d) k,
      algebraMap (MvPolynomial (Fin d) (K))
        (MvPolynomial (Fin d) (K) ⊗[MvPolynomial (Fin d) k] Cr)
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) (K)) x) =
      (1 : MvPolynomial (Fin d) (K)) ⊗ₜ
        algebraMap (MvPolynomial (Fin d) k) Cr x :=
    fun x => Algebra.TensorProduct.algebraMap_apply' x
  have hres := hSDZ (MvPolynomial (Fin d) (K))
    (MvPolynomial (Fin d) (K) ⊗[MvPolynomial (Fin d) k] Cr) Λ f' q d
    (fun i => (C (π i) * X i) ^ c)
    (fun i => by
      show algebraMap _ Λ ((C (π i) * X i) ^ c) ∈ q
      rw [map_pow, hγΛ]
      exact Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ (hpq i)) _ hc)
    (fun i x hx => by
      have hfun : (fun j => ((C (π j) * X j : MvPolynomial (Fin d) (K)) ^
          c) ^ 8) = fun j => (C (π j) * X j) ^ e := funext fun j => by rw [← pow_mul, hedef]
      have key := pow_annihilator (h12' i) hc x
      rw [← hfun] at key
      exact key hx)
    (fun i z hz => by
      have hfun : (fun j => algebraMap (MvPolynomial (Fin d) (K)) Λ
          ((C (π j) * X j) ^ c) ^ 8) = fun j => (δ j * φ (π j)) ^ e := funext fun j => by
        rw [map_pow, hγΛ, ← pow_mul, hedef]
      have hpi : algebraMap (MvPolynomial (Fin d) (K)) Λ
          ((C (π i) * X i) ^ c) = (δ i * φ (π i)) ^ c := by rw [map_pow, hγΛ]
      have key := pow_annihilator (h13' i) hc z
      rw [← hfun, ← hpi] at key
      exact key hz)
    (fun i => by
      show IsStrictlyStandard _ (algebraMap (MvPolynomial (Fin d) (K))
        (MvPolynomial (Fin d) (K) ⊗[MvPolynomial (Fin d) k] Cr)
        ((C (π i) * X i) ^ c))
      rw [← hγ, ← map_pow, hA'C]
      exact (hssC i).baseChange)
    (fun R₁ Λ₁ _ _ _ σ τ _ hτ hkσ _ hστ Q _ hQ => by
      have hσ0 : ∀ i, σ ((C (π i) * X i) ^ e) = 0 := fun i => by
        rw [← RingHom.mem_ker, hkσ, hedef, pow_mul]
        exact Ideal.subset_span ⟨i, rfl⟩
      exact bottom_condition φ q 𝔭 h𝔭 hn ψ hψ hES hψφ f hf N a π δ hδq lam w hlam hw e h𝔭n hqn
        hγ hγk (fun _ => rfl) rC fB hfBA hfBX hfBZ R₁ Λ₁ σ τ hτ hσ0 hστ Q hQ)
  -- Step 9: the resolution over `k`
  obtain ⟨D', _, _, _, gD, hD', hgh, hle, hnle⟩ := hres
  let : Algebra k D' :=
    ((algebraMap (MvPolynomial (Fin d) (K)) D').comp
      (algebraMap k (MvPolynomial (Fin d) (K)))).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin d) (K)) D' :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k (MvPolynomial (Fin d) (K)) Λ :=
    .of_algebraMap_eq fun c' => by
      show _ = eval₂Hom (φ : K →+* Λ) δ
        (C (algebraMap k (K) c'))
      rw [eval₂Hom_C]
      exact (φ.commutes c').symm
  have : Algebra.FinitePresentation k (MvPolynomial (Fin d) (K)) :=
    Algebra.FinitePresentation.trans k (K) _
  have : Algebra.Smooth k (MvPolynomial (Fin d) (K)) :=
    Algebra.Smooth.comp k (K) _
  have : Algebra.FinitePresentation k D' :=
    Algebra.FinitePresentation.trans k (MvPolynomial (Fin d) (K)) D'
  let ι : A →+* MvPolynomial (Fin d) (K) ⊗[MvPolynomial (Fin d) k] Cr :=
    (Algebra.TensorProduct.includeRight.toRingHom).comp
      (gC.toRingHom.comp (algebraMap A (Alg d (2 * N) a)))
  have hι : ∀ x, ι x = (1 : MvPolynomial (Fin d) (K)) ⊗ₜ
      gC (algebraMap A (Alg d (2 * N) a) x) := fun _ => rfl
  have hιk : ∀ c' : k, gD (ι (algebraMap k A c')) = algebraMap k D' c' := fun c' => by
    have e1 : algebraMap A (Alg d (2 * N) a) (algebraMap k A c') =
        algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (C c') :=
      (IsScalarTower.algebraMap_apply k A (Alg d (2 * N) a) c').symm.trans
        (IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Alg d (2 * N) a) c')
    rw [hι, e1, gC.commutes, ← hA'C, gD.commutes, hγk]
    try rfl
  let g' : A →ₐ[k] D' := { gD.toRingHom.comp ι with commutes' := hιk }
  let h' : D' →ₐ[k] Λ := hD'.restrictScalars k
  have hf'A : ∀ x, f' ((1 : MvPolynomial (Fin d) (K)) ⊗ₜ
      gC (algebraMap A (Alg d (2 * N) a) x)) = f x := fun x => by
    show (Algebra.TensorProduct.lift (Algebra.ofId _ Λ) (fB.comp rC)
      (fun _ _ => Commute.all _ _)) (_ ⊗ₜ _) = f x
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
      ← AlgHom.comp_apply rC gC, hrg, AlgHom.id_apply, hfBA]
  have hcomp : h'.comp g' = f := by
    ext x
    have h1 := congrArg (fun F => F ((1 : MvPolynomial (Fin d) (K)) ⊗ₜ
      gC (algebraMap A (Alg d (2 * N) a) x))) hgh
    simp only [AlgHom.comp_apply] at h1
    exact h1.trans (hf'A x)
  have hDle : singularRadical (MvPolynomial (Fin d) (K)) hD' ≤
      singularRadical k h' :=
    Ideal.radical_mono (Ideal.map_mono (singularIdeal_le_of_smooth k _ D'))
  refine ⟨D', inferInstance, inferInstance, inferInstance, g', h', hcomp, ?_,
    fun h => hnle (hDle.trans h)⟩
  show ((singularIdeal k A).map f).radical ≤ _
  refine (Ideal.radical_mono ?_).trans (Ideal.radical_isRadical _)
  rw [← ha', Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have h1 : gC (algebraMap A (Alg d (2 * N) a) (a j)) ∈
      singularIdeal (MvPolynomial (Fin d) k) Cr := by
    obtain ⟨c', hc'⟩ := hss _ (DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (hBa j))
    exact mem_singularIdeal_of_pow n0 hc'
  have h2 : f' ((1 : MvPolynomial (Fin d) (K)) ⊗ₜ
      gC (algebraMap A (Alg d (2 * N) a) (a j))) ∈ singularRadical _ f' :=
    Ideal.le_radical (Ideal.mem_map_of_mem _ (includeRight_mem_singularIdeal h1))
  rw [hf'A] at h2
  exact hDle (hle h2)

/-- Stacks Lemma 16.11.4 (07FJ), from the Library statements of its ingredients. -/
theorem charPResolution_of (n0 : StrictlyStandardSmoothStatement.{u})
    (n5 : StrictlyStandardRetractStatement.{u}) (hOg : AnnihilatorStabilizationStatement.{u})
    (h00NQ : RegularLocalParametersStatement.{u}) (h07DV : RegularSequencePowersStatement.{u})
    (h112 : ArtinianSmoothApproximationStatement.{u})
    (hSDZ : SequenceDimZeroResolutionStatement.{u}) : CharPResolutionStatement.{u} := by
  intro k A Λ _ _ _ _ _ _ p _ _ hreg f q _ hq
  classical
  have : IsNoetherianRing Λ := hreg.1
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  -- Step 1: generators `aⱼ` of `H_{A/k}` and the exponent `N`
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (singularIdeal k A))
  have ha' : Ideal.span (Set.range a) = singularIdeal k A := ha
  have hqI : q ∈ ((singularIdeal k A).map f).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes]; exact hq
  obtain ⟨N₀, hN₀⟩ := exists_pow_map_le _ q hqI
  obtain ⟨N, hNdef⟩ : ∃ N, N = N₀ + 1 := ⟨_, rfl⟩
  have hN : 1 ≤ N := by omega
  have hH : maximalIdeal (Localization.AtPrime q) ^ N ≤
      Ideal.span (Set.range fun j => algebraMap Λ (Localization.AtPrime q) (f (a j))) := by
    have h1 : maximalIdeal (Localization.AtPrime q) ^ N ≤
        (q ^ N₀).map (algebraMap Λ (Localization.AtPrime q)) := by
      rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.pow_le_pow_right (by omega)
    refine h1.trans (hN₀.trans (le_of_eq ?_))
    rw [← ha', Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    try rfl
  -- Step 2: `d`, the algebra `B`, its retract `C` and the exponents `c`, `e = 8c`, `n`
  obtain ⟨d, hd⟩ : ∃ d, (maximalIdeal (Localization.AtPrime q)).spanFinrank = d := ⟨_, rfl⟩
  have ha_mem : ∀ j, a j ∈ singularIdeal k A := fun j => by
    rw [← ha']; exact Ideal.subset_span ⟨j, rfl⟩
  have hBa : ∀ j, algebraMap A (Alg d (2 * N) a) (a j) ∈
      singularIdeal (MvPolynomial (Fin d) k) (Alg d (2 * N) a) := fun j => by
    have := DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (ha_mem j)
    exact DimZeroResolutionProof.mem_singularIdeal_of_smooth _ (SmoothingAlgebra.smooth_away d (2 * N) a k j)
  have hBx := SmoothingAlgebra.algebraMap_X_mem_singularIdeal d (2 * N) a k hBa
  obtain ⟨Cr, _, _, hCfp, gC, rC, hrg, hss⟩ := n5 (MvPolynomial (Fin d) k) (Alg d (2 * N) a)
  have hcx : ∀ i, ∃ c, IsStrictlyStandard (MvPolynomial (Fin d) k)
      (gC (algebraMap (MvPolynomial (Fin d) k) (Alg d (2 * N) a) (X i)) ^ c) := fun i =>
    hss _ (DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (hBx i))
  choose cx hcx using hcx
  obtain ⟨c, hcdef⟩ : ∃ c, c = ∑ i, cx i + 1 := ⟨_, rfl⟩
  have hc : 0 < c := by omega
  have hssC : ∀ i, IsStrictlyStandard (MvPolynomial (Fin d) k)
      (algebraMap (MvPolynomial (Fin d) k) Cr (X i ^ c)) := fun i => by
    have hle : cx i ≤ c := by
      have := Finset.single_le_sum (f := cx) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    rw [map_pow, ← gC.commutes, ← Nat.add_sub_cancel' hle, pow_add]
    exact (hcx i).mul_right _
  obtain ⟨e, hedef⟩ : ∃ e, e = c * 8 := ⟨_, rfl⟩
  have he : 0 < e := by omega
  obtain ⟨n, hndef⟩ : ∃ n, n = N + d * e := ⟨_, rfl⟩
  have hn1 : d * e + 1 ≤ n := by rw [hndef, add_comm N]; exact Nat.add_le_add_left hN _
  have hNn : N ≤ n := by rw [hndef]; exact Nat.le_add_right _ _
  have hn : 0 < n := Nat.lt_of_lt_of_le hN hNn
  -- Step 3: Lemma 11.2 for the truncation `Λ_q/qⁿΛ_q`
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  obtain ⟨m, φ, 𝔭, _, h𝔭, hmax, hflat, D, _, _, _, _, ψ, hES, _, hψ, hψφ, hE⟩ :=
    h112 k Λ p hreg q n hn (s.image fun x => toLocalTruncation q n (f x))
  have hf : ∀ x : A, ∃ b, ψ b = toLocalTruncation q n (f x) := by
    let S : Subalgebra k A :=
      { carrier := {x | ∃ b, ψ b = toLocalTruncation q n (f x)}
        mul_mem' := fun {x y} ⟨b1, h1⟩ ⟨b2, h2⟩ =>
          ⟨b1 * b2, by rw [map_mul, h1, h2, map_mul, map_mul]⟩
        add_mem' := fun {x y} ⟨b1, h1⟩ ⟨b2, h2⟩ =>
          ⟨b1 + b2, by rw [map_add, h1, h2, map_add, map_add]⟩
        algebraMap_mem' := fun c' =>
          ⟨algebraMap (localTruncation 𝔭 n) D
            (toLocalTruncation 𝔭 n (algebraMap k (MvPolynomial (Fin m) k) c')),
            by rw [hψφ, φ.commutes, f.commutes]⟩ }
    have hle : Algebra.adjoin k (s : Set A) ≤ S := Algebra.adjoin_le fun x hx =>
      hE (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    intro x
    exact hle (by rw [hs]; exact Algebra.mem_top)
  -- Step 4: the regular local ring `K_𝔭` and the flat local map `K_𝔭 → Λ_q`
  have : IsRegularLocalRing (Localization.AtPrime 𝔭) :=
    isRegularLocalRing_localization_atPrime_mvPolynomial k m 𝔭
  let : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime q) :=
    (Localization.localRingHom 𝔭 q (φ : MvPolynomial (Fin m) k →+* Λ) h𝔭).toAlgebra
  have : Module.Flat (Localization.AtPrime 𝔭) (Localization.AtPrime q) := hflat
  have : IsLocalHom (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ h𝔭
  have hloc : ∀ y : MvPolynomial (Fin m) k,
      algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)
        (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) y) =
      algebraMap Λ (Localization.AtPrime q) (φ y) :=
    fun y => Localization.localRingHom_to_map _ _ _ h𝔭 y
  have hmap : (maximalIdeal (Localization.AtPrime 𝔭)).map
      (algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := by
    rw [← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    exact RingHom.ext hloc
  have hdK : (maximalIdeal (Localization.AtPrime 𝔭)).spanFinrank = d := by
    apply le_antisymm
    · rw [← hd]; exact spanFinrank_le_of_flat _ _
    · rw [← hd, ← hmap]; exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
  -- Step 5: parameters `π` of `K_𝔭` and step (12)
  obtain ⟨y, hy⟩ : ∃ y : Fin d → Localization.AtPrime 𝔭,
      Ideal.span (Set.range y) = maximalIdeal (Localization.AtPrime 𝔭) := by
    rw [← hdK]; exact exists_fin_span_eq_of_fg (IsNoetherian.noetherian _)
  have hmk : ∀ i, ∃ (x : MvPolynomial (Fin m) k) (s' : 𝔭.primeCompl),
      IsLocalization.mk' (Localization.AtPrime 𝔭) x s' = y i :=
    fun i => by
      obtain ⟨⟨x, s'⟩, h⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl (y i)
      exact ⟨x, s', h⟩
  choose π0 s0 hπs using hmk
  have hspan0 : Ideal.span (Set.range fun i =>
      algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π0 i)) =
      maximalIdeal (Localization.AtPrime 𝔭) := by
    have h1 : (fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π0 i)) =
        fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (s0 i) * y i :=
      funext fun i => by rw [← hπs i, IsLocalization.mk'_spec']
    rw [h1, ← Set.image_univ, span_image_unit_mul y
      (fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (s0 i))
      (fun i => IsLocalization.map_units _ (s0 i)), Set.image_univ, hy]
  have hregK0 : ∀ (T : Finset (Fin d)) (i : Fin d), i ∉ T → ∀ z : Localization.AtPrime 𝔭,
      algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π0 i) * z ∈
        Ideal.span ((fun j => algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime 𝔭) (π0 j) ^ e) '' (T : Set (Fin d))) →
      z ∈ Ideal.span ((fun j => algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime 𝔭) (π0 j) ^ e) '' (T : Set (Fin d))) :=
    fun T i hi z hz => mem_of_mul_mem_span_pow h00NQ h07DV _ hdK hspan0 e he
      (L' := Localization.AtPrime 𝔭) T i hi z hz
  obtain ⟨s1, hs1, h12⟩ := exists_step12_poly hOg 𝔭 π0 e hregK0
  obtain ⟨π, hπdef⟩ : ∃ π : Fin d → MvPolynomial (Fin m) k, π = fun i => s1 i * π0 i :=
    ⟨_, rfl⟩
  have h12' : ∀ (i : Fin d) (x : MvPolynomial (Fin d) (MvPolynomial (Fin m) k)),
      (C (π i) * X i) ^ 2 * x ∈ Ideal.span ((fun j => (C (π j) * X j) ^ e) '' {j | j < i}) →
      C (π i) * X i * x ∈ Ideal.span ((fun j => (C (π j) * X j) ^ e) '' {j | j < i}) := by
    subst hπdef; exact h12
  have hu1 : ∀ i, IsUnit (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (s1 i)) :=
    fun i => IsLocalization.map_units _ (⟨s1 i, hs1 i⟩ : 𝔭.primeCompl)
  have hspan : Ideal.span (Set.range fun i =>
      algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π i)) =
      maximalIdeal (Localization.AtPrime 𝔭) := by
    have h1 : (fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π i)) =
        fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (s1 i) *
          algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π0 i) :=
      funext fun i => by rw [hπdef]; exact map_mul _ _ _
    rw [h1, ← Set.image_univ, span_image_unit_mul
      (fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π0 i)) _ hu1,
      Set.image_univ, hspan0]
  have hπ𝔭 : ∀ i, π i ∈ 𝔭 := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 (π i)).mp
      (by rw [← hspan]; exact Ideal.subset_span ⟨i, rfl⟩)
  have hpq : ∀ i, φ (π i) ∈ q := fun i => by
    have := hπ𝔭 i
    rw [h𝔭] at this
    exact this
  have h𝔭n : maximalIdeal (Localization.AtPrime 𝔭) ^ n ≤ Ideal.span (Set.range fun i =>
      algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π i ^ e)) := by
    have h1 := span_pow_le_span_pow e
      (fun i => algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔭) (π i))
    rw [hspan] at h1
    refine (Ideal.pow_le_pow_right hn1).trans ?_
    simp only [map_pow]
    exact h1
  have hqn : maximalIdeal (Localization.AtPrime q) ^ n ≤ Ideal.span (Set.range fun i =>
      algebraMap Λ (Localization.AtPrime q) (φ (π i) ^ e)) := by
    rw [← hmap, ← Ideal.map_pow]
    refine (Ideal.map_mono h𝔭n).trans (le_of_eq ?_)
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, map_pow, hloc]
  have hregΛ : ∀ (T : Finset (Fin d)) (i : Fin d), i ∉ T → ∀ z : Localization.AtPrime q,
      algebraMap Λ (Localization.AtPrime q) (φ (π i)) * z ∈
        Ideal.span ((fun j => algebraMap Λ (Localization.AtPrime q) (φ (π j)) ^ e) ''
          (T : Set (Fin d))) →
      z ∈ Ideal.span ((fun j => algebraMap Λ (Localization.AtPrime q) (φ (π j)) ^ e) ''
          (T : Set (Fin d))) := by
    intro T i hi z
    have key := mem_of_mul_mem_span_pow h00NQ h07DV _ hdK hspan e he
      (L' := Localization.AtPrime q) T i hi z
    simp only [hloc] at key
    exact key
  -- Step 6: step (13)
  obtain ⟨δ, hδq, hAdm, h13⟩ := exists_step13 hOg q hN hNn (fun j => f (a j)) hH ψ hψ
    (fun j => hf _) (fun i => φ (π i)) hpq (fun i => ⟨_, hψφ (π i)⟩) e hregΛ
  have hAdm' : ∀ i, ∃ lam : Fin r → Λ, (δ i * φ (π i)) ^ (2 * N) = ∑ j, lam j * f (a j) ∧
      ∀ j, ∃ w : D, toLocalTruncation q n (lam j) =
        toLocalTruncation q n (δ i) ^ (2 * N) * ψ w := hAdm
  choose lam hlam hw' using hAdm'
  choose w hw using hw'
  have h13' : ∀ (i : Fin d) (z : Λ), (δ i * φ (π i)) ^ 2 * z ∈
      Ideal.span ((fun j => (δ j * φ (π j)) ^ e) '' {j | j < i}) →
      δ i * φ (π i) * z ∈ Ideal.span ((fun j => (δ j * φ (π j)) ^ e) '' {j | j < i}) := h13
  -- Steps 7–9
  have : Algebra.Smooth k (MvPolynomial (Fin m) k) := {}
  exact resolution_of_parameters n0 hSDZ φ q 𝔭 h𝔭 hn ψ hψ hES hψφ f hf N a ha' π δ hδq lam w
    hlam hw e c hc hedef h𝔭n hqn hpq h12' h13' gC rC hrg hss hssC hBa

end Main

end Langlands.CommutativeAlgebra.Popescu.CharP
