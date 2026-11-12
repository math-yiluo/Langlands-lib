import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry

/-! # Euler polynomials at negative exponents through an inverse line bundle -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- If `M ⊗ N` is trivial, then `M^k ⊗ N^(j+k) ≅ N^j`, by cancelling one factor
`M ⊗ N` at a time. -/
def tensorPowInverseCancelIso (M N : X.Modules) (e : tensorObj M N ≅ structureSheaf X) :
    (k j : ℕ) → tensorObj (tensorPow M k) (tensorPow N (j + k)) ≅ tensorPow N j
  | 0, j => tensorLeftUnitor (tensorPow N j)
  | k + 1, j =>
      tensorMiddleFourIso M (tensorPow M k) N (tensorPow N (j + k)) ≪≫
        tensorMapIso e (tensorPowInverseCancelIso M N e k j) ≪≫
          tensorLeftUnitor (tensorPow N j)

/-- If `N ⊗ M` is trivial, then so is `N^n ⊗ M^n`, by pairing one factor `N ⊗ M` at a
time. -/
def tensorPowInverseIso (N M : X.Modules) (e : tensorObj N M ≅ structureSheaf X) :
    (n : ℕ) → tensorObj (tensorPow N n) (tensorPow M n) ≅ structureSheaf X
  | 0 => tensorLeftUnitor (structureSheaf X)
  | n + 1 =>
      tensorMiddleFourIso N (tensorPow N n) M (tensorPow M n) ≪≫
        tensorMapIso e (tensorPowInverseIso N M e n) ≪≫
          tensorLeftUnitor (structureSheaf X)

/-- Two inverses of the same module are isomorphic:
`B' ≅ O ⊗ B' ≅ (B ⊗ A) ⊗ B' ≅ B ⊗ (A ⊗ B') ≅ B ⊗ O ≅ B`. -/
def inverseUniqueIso {A B B' : X.Modules} (e : tensorObj A B ≅ structureSheaf X)
    (e' : tensorObj A B' ≅ structureSheaf X) : B' ≅ B :=
  (tensorLeftUnitor B').symm ≪≫
    tensorMapIso (tensorComm B A ≪≫ e).symm (Iso.refl B') ≪≫
      tensorAssociator B A B' ≪≫
        tensorMapIso (Iso.refl B) e' ≪≫
          tensorRightUnitor B

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Twisting `M^k` by `N^(j+k)` gives the Euler characteristic of `N^j` when `M ⊗ N` is
trivial. -/
lemma coherentEulerSequence_tensorPow_inverse (N M : LineBundle X)
    (e : tensorObj M.obj N.obj ≅ structureSheaf X) (k j : ℕ) :
    letI := (tensorPow_isLocallyFreeRankOne X M k).isQuasicoherent
    coherentEulerSequence f (tensorPow M.obj k)
        (hasFiniteAffineSections_lineBundle ⟨_, tensorPow_isLocallyFreeRankOne X M k⟩) N
        (j + k) =
      (eulerCharacteristic f (tensorPow N.obj j)
        (lineBundleTensorPow_hasFiniteCohomology f N j) : ℚ) := by
  let := (tensorPow_isLocallyFreeRankOne X M k).isQuasicoherent
  have hL := tensorPow_isLocallyFreeRankOne X N (j + k)
  let := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle (tensorPow M.obj k) _ hL
  change (eulerCharacteristic f (tensorObj (tensorPow M.obj k) (tensorPow N.obj (j + k))) _ :
    ℚ) = _
  exact congrArg (Int.cast : ℤ → ℚ)
    (eulerCharacteristic_eq_of_iso f _ _ (tensorPowInverseCancelIso M.obj N.obj e k j))

/-- The untwisted term of the Euler sequence of `M^k` is the Euler characteristic of
`M^k`. -/
lemma coherentEulerSequence_tensorPow_zero (M N : LineBundle X) (k : ℕ)
    (h : HasFiniteCohomology f (tensorPow M.obj k)) :
    letI := (tensorPow_isLocallyFreeRankOne X M k).isQuasicoherent
    coherentEulerSequence f (tensorPow M.obj k)
        (hasFiniteAffineSections_lineBundle ⟨_, tensorPow_isLocallyFreeRankOne X M k⟩) N 0 =
      (eulerCharacteristic f (tensorPow M.obj k) h : ℚ) := by
  let := (tensorPow_isLocallyFreeRankOne X M k).isQuasicoherent
  have hL := tensorPow_isLocallyFreeRankOne X N 0
  let := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle (tensorPow M.obj k) _ hL
  change (eulerCharacteristic f (tensorObj (tensorPow M.obj k) (structureSheaf X)) _ : ℚ) = _
  exact congrArg (Int.cast : ℤ → ℚ)
    (eulerCharacteristic_eq_of_iso f _ _ (tensorRightUnitor (tensorPow M.obj k)))

/-- The Euler polynomial of `N` evaluated at `-k` is `χ(M^k)` when `M ⊗ N` is trivial. -/
lemma lineBundleEulerPolynomial_eval_neg [IsNoetherian X] [X.IsSeparated]
    (N M : LineBundle X) (e' : tensorObj M.obj N.obj ≅ structureSheaf X)
    (d : ℕ) (hX : topologicalKrullDim X ≤ d) (k : ℕ)
    (h : HasFiniteCohomology f (tensorPow M.obj k)) :
    (lineBundleEulerPolynomial f N d).eval (-(k : ℚ)) =
      (eulerCharacteristic f (tensorPow M.obj k) h : ℚ) := by
  let := (tensorPow_isLocallyFreeRankOne X M k).isQuasicoherent
  have hMk := hasFiniteAffineSections_lineBundle
    ⟨tensorPow M.obj k, tensorPow_isLocallyFreeRankOne X M k⟩
  have hsupp := HasSupportDimensionLT.of_topologicalKrullDim_le hX (tensorPow M.obj k)
  have hQ : coherentEulerPolynomial f (tensorPow M.obj k) hMk N d =
      (lineBundleEulerPolynomial f N d).comp (Polynomial.X - C (k : ℚ)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => ((j + k : ℕ) : ℚ))
      (fun a b hab => by simpa using hab) fun j => ?_
    simp only [Set.mem_ofPred_eq, eval_comp, eval_sub, eval_X, eval_C]
    rw [coherentEulerPolynomial_eval f _ hMk N d hsupp,
      coherentEulerSequence_tensorPow_inverse f N M e' k j, Nat.cast_add, add_sub_cancel_right,
      lineBundleEulerPolynomial_eval f N d hX j]
  have h0 := coherentEulerPolynomial_eval f _ hMk N d hsupp 0
  rw [hQ, coherentEulerSequence_tensorPow_zero f M N k h] at h0
  simpa using h0

/-- **Integer-exponent Euler polynomial.** Let `N` and `M` be line bundles with `N ⊗ M`
trivial on a proper Noetherian separated scheme over a field, of topological Krull
dimension at most `d`. One rational polynomial of degree at most `d` gives `χ(N^n)` at `n`
and `χ(M^n)` at `-n` for every natural number `n`; at `-n` it also gives the Euler
characteristic of every module `Mn` with `N^n ⊗ Mn` trivial. -/
theorem exists_inverseLineBundleEulerPolynomial [IsNoetherian X] [X.IsSeparated]
    (N M : LineBundle X) (hNM : Nonempty (tensorObj N.obj M.obj ≅ structureSheaf X))
    (d : ℕ) (hX : topologicalKrullDim X ≤ d) :
    ∃ P : ℚ[X], P.natDegree ≤ d ∧
      (∀ (n : ℕ) (h : HasFiniteCohomology f (tensorPow N.obj n)),
        P.eval (n : ℚ) = (eulerCharacteristic f (tensorPow N.obj n) h : ℚ)) ∧
      (∀ (n : ℕ) (h : HasFiniteCohomology f (tensorPow M.obj n)),
        P.eval (-(n : ℚ)) = (eulerCharacteristic f (tensorPow M.obj n) h : ℚ)) ∧
      (∀ (n : ℕ) (Mn : X.Modules),
        Nonempty (tensorObj (tensorPow N.obj n) Mn ≅ structureSheaf X) →
          ∀ h : HasFiniteCohomology f Mn,
            P.eval (-(n : ℚ)) = (eulerCharacteristic f Mn h : ℚ)) := by
  obtain ⟨e⟩ := hNM
  let e' : tensorObj M.obj N.obj ≅ structureSheaf X := tensorComm M.obj N.obj ≪≫ e
  have hneg := lineBundleEulerPolynomial_eval_neg f N M e' d hX
  refine ⟨lineBundleEulerPolynomial f N d, lineBundleEulerPolynomial_natDegree_le f N d,
    fun n h => lineBundleEulerPolynomial_eval f N d hX n h, hneg, fun n Mn hMn h => ?_⟩
  obtain ⟨e₂⟩ := hMn
  have h' := lineBundleTensorPow_hasFiniteCohomology f M n
  rw [hneg n h', eulerCharacteristic_eq_of_iso f h h'
    (inverseUniqueIso (tensorPowInverseIso N.obj M.obj e n) e₂)]

/-- **Closing algebra.** If a rational polynomial satisfies `P(k) P(-k) = c k^(2g)` for every
positive integer `k`, then `P(-1) = (-1)^g P(1)`. No degree bound is needed: the identity
forces `P(X) P(-X) = c X^(2g)`, so either `P = 0` or `P` is a constant times a power of the
prime `X`, and the evaluations at `1` and `2` force that power to be `X^g`. -/
theorem polynomial_eval_neg_one_of_eval_mul_eval_neg (g : ℕ) (P : ℚ[X]) (c : ℚ)
    (h : ∀ k : ℕ, 1 ≤ k → P.eval (k : ℚ) * P.eval (-(k : ℚ)) = c * (k : ℚ) ^ (2 * g)) :
    P.eval (-1) = (-1) ^ g * P.eval 1 := by
  have hQ : P * P.comp (-Polynomial.X) = C c * Polynomial.X ^ (2 * g) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => ((j + 1 : ℕ) : ℚ))
      (fun a b hab => by simpa using hab) fun j => ?_
    simp only [Set.mem_ofPred_eq, eval_mul, eval_comp, eval_neg, eval_X, eval_C, eval_pow]
    exact h (j + 1) (by omega)
  by_cases hc : c = 0
  · subst hc
    have hP : P = 0 := by simpa using hQ
    simp [hP]
  · have hdvd : P ∣ Polynomial.X ^ (2 * g) :=
      (IsUnit.dvd_mul_left (isUnit_C.mpr (Ne.isUnit hc))).mp ⟨_, hQ.symm⟩
    obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow prime_X _).mp hdvd
    obtain ⟨a, -, ha⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
    have hPa : P = C a * Polynomial.X ^ i := by
      rw [ha, ← hu, mul_comm, Units.mul_inv_cancel_right]
    have hev : ∀ x : ℚ, P.eval x = a * x ^ i := fun x => by simp [hPa]
    have h1 := h 1 le_rfl
    have h2 := h 2 (by norm_num)
    simp only [hev, Nat.cast_one, one_pow, mul_one, Nat.cast_ofNat] at h1 h2
    have hc' : a * (-1) ^ i * a ≠ 0 := by
      intro h0
      exact hc (by rw [← h1, ← h0]; ring)
    have h4 : ((4 ^ i : ℕ) : ℚ) = ((4 ^ g : ℕ) : ℚ) := by
      apply mul_left_cancel₀ hc'
      push_cast
      calc a * (-1) ^ i * a * 4 ^ i = a * 2 ^ i * (a * (-2) ^ i) := by
            rw [show (4 : ℚ) = 2 * 2 by norm_num, show (-2 : ℚ) = -1 * 2 by norm_num, mul_pow,
              mul_pow]
            ring
        _ = c * 2 ^ (2 * g) := h2
        _ = a * (-1) ^ i * a * 4 ^ g := by
            rw [← h1, pow_mul]
            norm_num
            ring
    have hig : i = g := Nat.pow_right_injective (le_refl 2) (by
      simpa [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul] using (Nat.cast_injective h4 :
        4 ^ i = 4 ^ g))
    subst hig
    rw [hev, hev]
    ring

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- **Integer-exponent Euler polynomial on an abelian variety.** On an abelian scheme of
relative dimension `g` over a field, if `N ⊗ M` is trivial then one rational polynomial `P`
of degree at most `g` satisfies `P(n) = χ(N^n)` and `P(-n) = χ(M^n)` for every natural
number `n`, and `P(-n) = χ(Mn)` for every module `Mn` with `N^n ⊗ Mn` trivial; in particular
`P(1) = χ(N)` and `P(-1) = χ(M)`. -/
theorem field_exists_inverseLineBundleEulerPolynomial {K : Type u} [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : A.HasRelativeDimension g)
    (N M : LineBundle A.X.left)
    (hNM : Nonempty (tensorObj N.obj M.obj ≅ structureSheaf A.X.left)) :
    ∃ P : ℚ[X], P.natDegree ≤ g ∧
      (∀ (n : ℕ) (h : HasFiniteCohomology A.X.hom (tensorPow N.obj n)),
        P.eval (n : ℚ) = (eulerCharacteristic A.X.hom (tensorPow N.obj n) h : ℚ)) ∧
      (∀ (n : ℕ) (h : HasFiniteCohomology A.X.hom (tensorPow M.obj n)),
        P.eval (-(n : ℚ)) = (eulerCharacteristic A.X.hom (tensorPow M.obj n) h : ℚ)) ∧
      (∀ (n : ℕ) (Mn : A.X.left.Modules),
        Nonempty (tensorObj (tensorPow N.obj n) Mn ≅ structureSheaf A.X.left) →
          ∀ h : HasFiniteCohomology A.X.hom Mn,
            P.eval (-(n : ℚ)) = (eulerCharacteristic A.X.hom Mn h : ℚ)) ∧
      (∀ h : HasFiniteCohomology A.X.hom N.obj,
        P.eval 1 = (eulerCharacteristic A.X.hom N.obj h : ℚ)) ∧
      (∀ h : HasFiniteCohomology A.X.hom M.obj,
        P.eval (-1) = (eulerCharacteristic A.X.hom M.obj h : ℚ)) := by
  have := field_isNoetherian A
  have := field_isSeparated A
  obtain ⟨P, hdeg, hpos, hneg, hinv⟩ := exists_inverseLineBundleEulerPolynomial A.X.hom N M
    hNM g (field_topologicalKrullDim hg).le
  refine ⟨P, hdeg, hpos, hneg, hinv, fun h => ?_, fun h => ?_⟩
  · have h1 := lineBundleTensorPow_hasFiniteCohomology A.X.hom N 1
    rw [← eulerCharacteristic_eq_of_iso A.X.hom h1 h (tensorPowOneIso N.obj), ← hpos 1 h1,
      Nat.cast_one]
  · have h1 := lineBundleTensorPow_hasFiniteCohomology A.X.hom M 1
    rw [← eulerCharacteristic_eq_of_iso A.X.hom h1 h (tensorPowOneIso M.obj), ← hneg 1 h1,
      Nat.cast_one]

/-- **Inverse symmetry from the product identity.** On an abelian scheme of relative
dimension `g` over a field, let `N ⊗ M` be trivial. If `χ(N^k) χ(M^k) = c k^(2g)` for every
positive integer `k`, then `χ(M) = (-1)^g χ(N)`. -/
theorem field_eulerCharacteristic_inverse_of_mul_eq {K : Type u} [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : A.HasRelativeDimension g)
    (N M : LineBundle A.X.left)
    (hNM : Nonempty (tensorObj N.obj M.obj ≅ structureSheaf A.X.left)) (c : ℤ)
    (hprod : ∀ k : ℕ, 1 ≤ k →
      ∀ (hNk : HasFiniteCohomology A.X.hom (tensorPow N.obj k))
        (hMk : HasFiniteCohomology A.X.hom (tensorPow M.obj k)),
        eulerCharacteristic A.X.hom (tensorPow N.obj k) hNk *
            eulerCharacteristic A.X.hom (tensorPow M.obj k) hMk =
          c * (k : ℤ) ^ (2 * g))
    (hN : HasFiniteCohomology A.X.hom N.obj) (hM : HasFiniteCohomology A.X.hom M.obj) :
    eulerCharacteristic A.X.hom M.obj hM = (-1) ^ g * eulerCharacteristic A.X.hom N.obj hN := by
  obtain ⟨P, -, hpos, hneg, -, h1, hm1⟩ :=
    field_exists_inverseLineBundleEulerPolynomial A g hg N M hNM
  have key := polynomial_eval_neg_one_of_eval_mul_eval_neg g P c fun k hk => by
    rw [hpos k (lineBundleTensorPow_hasFiniteCohomology A.X.hom N k),
      hneg k (lineBundleTensorPow_hasFiniteCohomology A.X.hom M k)]
    exact_mod_cast hprod k hk _ _
  rw [hm1 hM, h1 hN] at key
  exact_mod_cast key

end Langlands.AbelianScheme
