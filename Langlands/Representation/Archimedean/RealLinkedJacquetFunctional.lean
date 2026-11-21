import Langlands.Representation.Archimedean.RealTaylorLeftPolynomial
import Langlands.Representation.Archimedean.RealLinkedQuotientGrowth
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# A Jacquet functional killed by a power of a lower root vector, and slow growth of a quotient

`RealLinkedJacquetFunctionalStatement`: for a Langlands-ordered list `ds` of real blocks of total
rank `n` with two linked Mœglin data, the `O(n)`-finite functions `I(ds)` of the standard module
carry a nonzero real Jacquet functional `ℓ` with exponents `a` and signs `e`, a position `p` with
`p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and `ℓ ∘ π(E_{p+1,p})^k = 0`.

`realLinkedQuotientGrowth_of_split` proves that this statement,
`RealLeftPolynomialGrowthStatement` and `RealTaylorLeftPolynomialStatement` imply
`RealLinkedQuotientGrowthStatement`. The Frobenius map `B v (b κ) = χ(b) ℓ(ρ(κ) v)` of
`realJacquetFrobenius` sends `I(ds)` into a principal series; by the Taylor statement its image
consists of functions polynomial of degree `< k` along `t ↦ 1 + t E_{p+1,p}` on the left, so the
growth statement bounds the operators on the image, and these dominate the operators on
`I(ds) / ker B`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Algebra.UniversalEnveloping

/-- **A Jacquet functional killed by a power of a lower root vector.** For a list `ds` of real
blocks of total rank `n` in Langlands order, two of whose Mœglin data are linked, there are a
nonzero real Jacquet functional `ℓ` on the `O(n)`-finite functions of the standard module of
`ds`, with exponents `a` and signs `e` (`IsRealJacquetFunctional`), a position `p` with
`p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and `ℓ(π(E_{p+1,p})^k v) = 0` for
every `v`, where `π(E_{p+1,p})` is the action of `1 ⊗ E_{p+1,p}` through `realStandardLie n ds`. -/
def RealLinkedJacquetFunctionalStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
    ¬ IsRealMoeglinUnlinked ds →
      ∃ (ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
        (a : Fin n → ℂ) (e : Fin n → Fin 2) (p k : ℕ) (hp : p + 1 < n),
        ℓ ≠ 0 ∧ IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e ∧
          a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ) ∧
          ∀ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
            ℓ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n p hp) ^ k) v) = 0

namespace RealLinkedJacquetFunctional

open RealJacquetFrobenius

/-- If `g = Φ ∘ f` on a finite-dimensional subspace `P`, then `g(P)` has rank at most that of
`f(P)`. -/
theorem finrank_map_le_of_eqOn {K A E F : Type*} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    (P : Submodule K A) [Module.Finite K P] (f : A →ₗ[K] E) (g : A →ₗ[K] F) (Φ : E →ₗ[K] F)
    (h : ∀ x ∈ P, g x = Φ (f x)) :
    Module.finrank K (P.map g) ≤ Module.finrank K (P.map f) := by
  have hle : P.map g ≤ (P.map f).map Φ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, (h x hx).symm⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le Φ (P.map f))

section Quotient

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {X V : Type*} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup V] [Module ℂ V]

/-- For an intertwiner `B : X → V`, the operators of a finite-dimensional subspace `P` of `U(L)`
on `X / ker B` span a space of rank at most that of their restrictions `range B → V`: with a
left inverse `L'` of the injection `X / ker B → V`, the operator of `u` on `X / ker B` is
`L' ∘ (u|_{range B}) ∘ B`. -/
theorem finrank_quotient_ker_le (σ : L →ₗ⁅ℂ⁆ Module.End ℂ X) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (B : X →ₗ[ℂ] V) (h : ∀ (Y : L) (f : X), B (σ Y f) = π Y (B f))
    (P : Submodule ℂ (UniversalEnvelopingAlgebra ℂ L)) [Module.Finite ℂ P] :
    Module.finrank ℂ (P.map (LinearMap.llcomp ℂ X X (X ⧸ LinearMap.ker B)
        (LinearMap.ker B).mkQ ∘ₗ (envelopingAction σ).toLinearMap)) ≤
      Module.finrank ℂ (P.map (LinearMap.lcomp ℂ V (LinearMap.range B).subtype ∘ₗ
        (envelopingAction π).toLinearMap)) := by
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective
    ((LinearMap.ker B).liftQ B le_rfl) (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  refine finrank_map_le_of_eqOn P _ _
    (LinearMap.llcomp ℂ X V (X ⧸ LinearMap.ker B) L' ∘ₗ
      LinearMap.lcomp ℂ V B.rangeRestrict) fun u _ => ?_
  refine LinearMap.ext fun v => ?_
  change (LinearMap.ker B).mkQ (envelopingAction σ u v) =
    L' (envelopingAction π u (B v))
  rw [← envelopingAction_intertwine σ π B h u v]
  exact (LinearMap.congr_fun hL' ((LinearMap.ker B).mkQ (envelopingAction σ u v))).symm

end Quotient

section Frobenius

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {ℓ : V →ₗ[ℂ] ℂ}
  {a : Fin n → ℂ} {e : Fin n → Fin 2}

/-- `x ↦ sgn(x)^e |x|^t` is `x^t` for `x > 0`. -/
theorem charFun_of_pos (e : Fin 2) (t : ℂ) {x : ℝ} (hx : 0 < x) :
    charFun e t x = (x : ℂ) ^ t := by
  unfold charFun
  rw [abs_of_pos hx, div_self hx.ne', Complex.ofReal_one, one_pow, one_mul]

/-- The Frobenius function of `v` takes the value `ℓ(v)` at the identity. -/
theorem frobFun_apply_one
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (v : V) : frobFun ρ ℓ a e v 1 = ℓ v := by
  rw [frobFun_eq (b := 1) (k := 1) hsign Matrix.blockTriangular_one (one_mem _) (by simp) v,
    diagChar_one, one_mul]
  change ℓ (ρ 1 v) = ℓ v
  rw [map_one, Module.End.one_apply]

/-- `R(X)^k (B v) = B(π(X)^k v)`. -/
theorem iterate_rightDerivative_frobFun (hgk : IsRealGKModule n ρ π)
    (hℓ : IsRealJacquetFunctional n ρ π ℓ a e) (X : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (v : V) :
    (rightDerivative (matrixModel ℝ n) X)^[k] (frobFun ρ ℓ a e v) =
      frobFun ρ ℓ a e ((π (1 ⊗ₜ X) ^ k) v) := by
  induction k generalizing v with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, Module.End.one_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply,
      ← funext fun g => frobFun_rightDerivative hgk hℓ X v g, ih, pow_succ,
      Module.End.mul_apply]

/-- The Frobenius map into the `O(n)`-finite functions of a real standard module carries `π` to
the right-derivative action. -/
theorem frobLin_codRestrict_lie (hgk : IsRealGKModule n ρ π)
    (hℓ : IsRealJacquetFunctional n ρ π ℓ a e) {ds' : List RealBlock}
    (hmem : ∀ v : V, frobLin ρ ℓ a e v ∈
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : V) :
    (frobLin ρ ℓ a e).codRestrict _ hmem (π Y v) =
      realStandardLie n ds' Y ((frobLin ρ ℓ a e).codRestrict _ hmem v) := by
  induction Y using TensorProduct.inductionOn with
  | tmul c M =>
    have hc : (c ⊗ₜ[ℝ] M : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = c • ((1 : ℂ) ⊗ₜ[ℝ] M) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, LinearMap.smul_apply, map_smul, map_smul, LinearMap.smul_apply]
    congr 1
    apply Subtype.ext
    rw [realStandardLie_one_tmul_apply_coe]
    funext g
    exact frobFun_rightDerivative hgk hℓ M v g
  | add Y Z hY hZ =>
    rw [map_add, LinearMap.add_apply, map_add, hY, hZ, map_add, LinearMap.add_apply]

/-- The Frobenius map into the `O(n)`-finite functions of a real standard module carries `ρ` to
right translation. -/
theorem frobLin_codRestrict_rep
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    {ds' : List RealBlock}
    (hmem : ∀ v : V, frobLin ρ ℓ a e v ∈
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (κ : Matrix.unitaryGroup (Fin n) ℝ) (v : V) :
    (frobLin ρ ℓ a e).codRestrict _ hmem (ρ κ v) =
      realStandardRep n ds' κ ((frobLin ρ ℓ a e).codRestrict _ hmem v) := by
  apply Subtype.ext
  rw [realStandardRep_apply_coe]
  exact frobFun_rightTranslation hsign ⟨Unitary.toUnits κ, κ.2⟩ v

end Frobenius

/-- Once a Jacquet functional satisfies the exponent shift and the lower-root power
condition, the standard module has a proper quotient of slow growth. No ordering
hypothesis on `ds` is needed for this step. -/
theorem quotientGrowth_of_functional (hS1 : RealLeftPolynomialGrowthStatement)
    (hS3 : RealTaylorLeftPolynomialStatement) {n : ℕ} {ds : List RealBlock}
    {ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ}
    {a : Fin n → ℂ} {e : Fin n → Fin 2} {p k : ℕ} {hp : p + 1 < n}
    (hℓ0 : ℓ ≠ 0)
    (hℓ : IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e)
    (ha : a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ))
    (hY : ∀ v, ℓ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n p hp) ^ k) v) = 0) :
    ∃ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W ∧ W ≠ ⊤ ∧
      ∃ C : ℝ, ∀ d : ℕ,
        (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
          (LinearMap.llcomp ℂ _ _ _ W.mkQ ∘ₗ
            (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℝ) ≤
          C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1) := by
  have hgk := isRealGKModule_realStandardModule n ds
  have hsign : ∀ (j : Fin n)
      (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      ℓ (realStandardRep n ds (signReflection n j) v) = (-1) ^ (e j).val * ℓ v :=
    fun j v => (hℓ.2 j v).2
  have hPS : ∀ v, frobFun (realStandardRep n ds) ℓ a e v ∈ principalSeries ℝ n (posChar a e) :=
    fun v => (mem_principalSeries_iff ℝ n _ _).mpr
      ⟨contMDiff_frobFun hsign hgk.1 hgk.2.1 v, frobFun_left hsign v⟩
  have hmem : ∀ v, frobLin (realStandardRep n ds) ℓ a e v ∈ kFiniteFunctions
      (realStandardModule n ((List.ofFn (chars a e)).map RealBlock.character))
      (unitaryCompact ℝ n) := by
    intro v
    refine Submodule.mem_inf.mpr ⟨⟨hPS v, ?_⟩, frobFun_mem_kFiniteVectors hsign v (hgk.1 v)⟩
    intro q d hd
    rw [RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
    exact absurd hd (by simp)
  have hlie := frobLin_codRestrict_lie hgk hℓ hmem
  have hrep := frobLin_codRestrict_rep hsign hmem
  -- The exponent condition `χ_{p+1}(x) = x^k χ_p(x)` for `x > 0`.
  have hχ : ∀ x : ℝˣ, 0 < (x : ℝ) →
      posChar a e (p + 1) x = ((x : ℝ) : ℂ) ^ k * posChar a e p x := by
    intro x hx
    have h1 : posChar a e (p + 1) x =
        charFun (e ⟨p + 1, hp⟩) (expo a ⟨p + 1, hp⟩) x := posChar_apply a e ⟨p + 1, hp⟩ x
    have h0 : posChar a e p x =
        charFun (e ⟨p, Nat.lt_of_succ_lt hp⟩) (expo a ⟨p, Nat.lt_of_succ_lt hp⟩) x :=
      posChar_apply a e ⟨p, Nat.lt_of_succ_lt hp⟩ x
    have hexp : expo a ⟨p + 1, hp⟩ = expo a ⟨p, Nat.lt_of_succ_lt hp⟩ + (k : ℂ) := by
      simp only [expo]
      push_cast
      linear_combination -ha
    rw [h1, h0, charFun_of_pos _ _ hx, charFun_of_pos _ _ hx, hexp,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_natCast, mul_comm]
  -- The Taylor condition on `O(n)`.
  have htaylor : ∀ v, ∀ κ ∈ unitaryCompact ℝ n,
      (rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp))^[k]
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) κ
          (frobFun (realStandardRep n ds) ℓ a e v)) 1 = 0 := by
    intro v κ hκ
    rw [← frobFun_rightTranslation hsign ⟨κ, hκ⟩ v, iterate_rightDerivative_frobFun hgk hℓ,
      frobFun_apply_one hsign]
    exact hY _
  set B := (frobLin (realStandardRep n ds) ℓ a e).codRestrict _ hmem with hB
  have hpoly : ∀ h ∈ LinearMap.range B, ∀ g : Langlands.GeneralLinear n ℝ,
      ∃ q : Polynomial ℂ, q.degree < k ∧ ∀ t : ℝ,
        (h : Langlands.GeneralLinear n ℝ → ℂ) (lowerRootElement n p hp t * g) =
          q.eval (t : ℂ) := by
    rintro _ ⟨v, rfl⟩ g
    exact hS3 n (posChar a e) p k hp hχ _ (hPS v) (htaylor v) g
  obtain ⟨C, hC⟩ := hS1 n _ p k hp (LinearMap.range B) hpoly
  refine ⟨LinearMap.ker B, ⟨fun κ w hw => ?_, fun Y w hw => ?_⟩, ?_, C, fun d => ?_⟩
  · rw [LinearMap.mem_ker, hrep, LinearMap.mem_ker.1 hw, map_zero]
  · rw [LinearMap.mem_ker, hlie, LinearMap.mem_ker.1 hw, map_zero]
  · intro htop
    apply hℓ0
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker B := htop ▸ Submodule.mem_top
    have h0 : frobFun (realStandardRep n ds) ℓ a e v 1 = 0 :=
      congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hv)) 1
    rw [← frobFun_apply_one hsign v, h0, LinearMap.zero_apply]
  · exact (Nat.cast_le.mpr (finrank_quotient_ker_le _ _ B hlie _)).trans (hC d)

end RealLinkedJacquetFunctional

/-- **Slow growth of a quotient from the three statements.** -/
theorem realLinkedQuotientGrowth_of_split (hS1 : RealLeftPolynomialGrowthStatement)
    (hS3 : RealTaylorLeftPolynomialStatement) (hS2 : RealLinkedJacquetFunctionalStatement) :
    RealLinkedQuotientGrowthStatement := by
  intro n ds hrank hord hlink
  obtain ⟨ℓ, a, e, p, k, hp, hℓ0, hℓ, ha, hY⟩ := hS2 n ds hrank hord hlink
  exact RealLinkedJacquetFunctional.quotientGrowth_of_functional hS1 hS3 hℓ0 hℓ ha hY

end Langlands.Archimedean
