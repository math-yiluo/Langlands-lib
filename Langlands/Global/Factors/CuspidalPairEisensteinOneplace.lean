import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellExhaustion
import Langlands.Representation.Shahidi.UnramifiedOpenCellSection
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationReduction
import Langlands.Global.RankinSelberg.ArchimedeanDeterminantProducts

/-! # The open-cell integrand at one unramified place

Invariance properties of the twisted section `φ_s = φ · H^s` and of its Levi Whittaker
coefficient, used for the one-place factorization of the open-cell integrand. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairEisenstein.Oneplace

open MeasureTheory NumberField Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight
open scoped CategoryTheory.MonObj

local instance oneplaceSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (RankinSelbergGlobal.Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance oneplaceSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (RankinSelbergGlobal.Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance oneplaceGLAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance oneplaceGLSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

/-- The twisted section `φ_s = φ · H^s`. -/
def twisted (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) (g : AdelicGL F (r + t + 2)) : ℂ :=
  φ g * heightPower F r t s g

variable (F r t) in
theorem exists_parabolic_factor' (g : AdelicGL F (r + t + 2)) :
    ∃ p : Full F (blockShape r t), ∃ k ∈ standardCompact F (r + t + 2), p.val * k = g := by
  obtain ⟨p, k, hg, hp, hk⟩ := exists_isStandardIwasawaFactorization F (r + t + 2) g
  exact ⟨⟨p, (blockShape r t).upperTriangularSubgroup_le_parabolic (Adeles F) hp⟩, k, hk,
    hg.symm⟩

/-- `H^s` is right invariant under the standard maximal compact subgroup. -/
theorem heightPower_mul_compact (s : ℂ) (g k : AdelicGL F (r + t + 2))
    (hk : k ∈ standardCompact F (r + t + 2)) :
    heightPower F r t s (g * k) = heightPower F r t s g := by
  obtain ⟨p, k₀, hk₀, hg⟩ := exists_parabolic_factor' F r t g
  rw [heightPower_eq s p (Subgroup.mul_mem _ hk₀ hk) (by rw [← mul_assoc, hg]),
    heightPower_eq s p hk₀ hg]

/-- `H^s` is left invariant under the unipotent radical of `P(𝔸)`. -/
theorem heightPower_unipotent_mul (s : ℂ) (n g : AdelicGL F (r + t + 2))
    (hn : n ∈ (blockShape r t).unipotentSubgroup (Adeles F)) :
    heightPower F r t s (n * g) = heightPower F r t s g := by
  obtain ⟨h, hh, rfl⟩ := hn
  obtain ⟨p, k₀, hk₀, hg⟩ := exists_parabolic_factor' F r t g
  have e : (h * p : Full F (blockShape r t)).val * k₀ = h.val * g := by
    rw [Subgroup.coe_mul, mul_assoc, hg]
  show heightPower F r t s (h.val * g) = _
  rw [heightPower_eq s (h * p) hk₀ e, heightPower_eq s p hk₀ hg, map_mul,
    show parabolicCharacter F (blockShape r t) h = 1 from parabolicCharacter_unipotent F _ ⟨h, hh⟩,
    one_mul]

/-- The value of `H^s` at `m k`, for `m` in the adelic Levi and `k` in the standard maximal
compact subgroup. -/
theorem heightPower_levi_mul (s : ℂ) (m : FullLevi F (blockShape r t))
    (k : AdelicGL F (r + t + 2)) (hk : k ∈ standardCompact F (r + t + 2)) :
    heightPower F r t s ((blockShape r t).leviEmbedding (Adeles F) m * k) =
      Complex.exp (s / ((r + t + 2 : ℕ) : ℂ) *
        (Real.log ((leviCharacter F (blockShape r t) m : NNReal) : ℝ) : ℂ)) := by
  have h := heightPower_eq (r := r) (t := t) s
    ((blockShape r t).leviInParabolic (Adeles F) m) hk rfl
  rw [parabolicCharacter_section] at h
  exact h

/-- Right translation commutes with the Levi Whittaker coefficient. -/
theorem leviWhittaker_mul_right (ψ : AddChar (Adeles F) ℂ) (f : AdelicGL F (r + t + 2) → ℂ)
    (g h : AdelicGL F (r + t + 2)) :
    leviWhittaker F r t ψ f (g * h) = leviWhittaker F r t ψ (fun x => f (x * h)) g := by
  simp only [leviWhittaker, mul_assoc]

/-- The Levi Whittaker coefficient of a function right invariant under `h` is right invariant
under `h`. -/
theorem leviWhittaker_mul_right_of_invariant (ψ : AddChar (Adeles F) ℂ)
    (f : AdelicGL F (r + t + 2) → ℂ) (g h : AdelicGL F (r + t + 2))
    (hf : ∀ x, f (x * h) = f x) :
    leviWhittaker F r t ψ f (g * h) = leviWhittaker F r t ψ f g := by
  rw [leviWhittaker_mul_right]
  simp only [hf]

theorem leviPair_eq_leviInParabolic (x : AdelicGL F (r + 1)) (y : AdelicGL F (t + 1)) :
    leviPair F r t x y = ((blockShape r t).leviInParabolic (Adeles F)
      ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm (x, y))).val :=
  rfl

/-- Conjugation by a Levi element preserves the unipotent radical of `P(𝔸)`. -/
theorem leviPair_conj_mem (x : AdelicGL F (r + 1)) (y : AdelicGL F (t + 1))
    (n : AdelicGL F (r + t + 2)) (hn : n ∈ (blockShape r t).unipotentSubgroup (Adeles F)) :
    leviPair F r t x y * n * (leviPair F r t x y)⁻¹ ∈
      (blockShape r t).unipotentSubgroup (Adeles F) := by
  obtain ⟨h, hh, rfl⟩ := hn
  set q := (blockShape r t).leviInParabolic (Adeles F)
    ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm (x, y))
  refine ⟨q * h * q⁻¹, ((blockShape r t).unipotentRadicalNormal (Adeles F)).conj_mem h hh q, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

/-- The Levi Whittaker coefficient of a function left invariant under the unipotent radical
of `P(𝔸)` is left invariant under it. -/
theorem leviWhittaker_unipotent_mul (ψ : AddChar (Adeles F) ℂ) (f : AdelicGL F (r + t + 2) → ℂ)
    (hf : ∀ n ∈ (blockShape r t).unipotentSubgroup (Adeles F), ∀ g, f (n * g) = f g)
    (n g : AdelicGL F (r + t + 2)) (hn : n ∈ (blockShape r t).unipotentSubgroup (Adeles F)) :
    leviWhittaker F r t ψ f (n * g) = leviWhittaker F r t ψ f g := by
  have key : ∀ (x : AdelicGL F (r + 1)) (y : AdelicGL F (t + 1)),
      f (leviPair F r t x y * (n * g)) = f (leviPair F r t x y * g) := by
    intro x y
    have e : leviPair F r t x y * (n * g) =
        (leviPair F r t x y * n * (leviPair F r t x y)⁻¹) * (leviPair F r t x y * g) := by
      group
    rw [e, hf _ (leviPair_conj_mem x y n hn)]
  simp only [leviWhittaker, key]

/-- The twisted section of a section is left invariant under the unipotent radical. -/
theorem twisted_unipotent_mul [CompactSpace (AdeleQuotient F)]
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    {φ : AdelicGL F (r + t + 2) → ℂ} (hφ : IsSection T T' φ) (s : ℂ) :
    ∀ n ∈ (blockShape r t).unipotentSubgroup (Adeles F), ∀ g,
      twisted φ s (n * g) = twisted φ s g := by
  intro n hn g
  rw [twisted, twisted, heightPower_unipotent_mul s n g hn, hφ.2.2.2.1 ⟨n, hn⟩ g]

/-- The adelic Levi element `diag(x, z)`. -/
abbrev leviOf (x : AdelicGL F (r + 1)) (z : AdelicGL F (t + 1)) : FullLevi F (blockShape r t) :=
  (Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm (x, z)

theorem leviPair_eq_leviEmbedding (x : AdelicGL F (r + 1)) (z : AdelicGL F (t + 1)) :
    leviPair F r t x z = (blockShape r t).leviEmbedding (Adeles F) (leviOf x z) :=
  rfl

theorem leviCharacter_leviOf (x : AdelicGL F (r + 1)) (z : AdelicGL F (t + 1)) :
    leviCharacter F (blockShape r t) (leviOf x z) =
      determinantNorm F (r + 1) x ^ (t + 1) / determinantNorm F (t + 1) z ^ (r + 1) := by
  rw [leviCharacter_apply]
  show (∏ i : Fin 2, ∏ j ∈ Finset.univ.filter (fun j : Fin 2 => i < j),
      determinantNorm F (![r + 1, t + 1] i) (leviOf x z i) ^ ![r + 1, t + 1] j /
        determinantNorm F (![r + 1, t + 1] j) (leviOf x z j) ^ ![r + 1, t + 1] i) = _
  simp only [Finset.prod_filter, Fin.prod_univ_two]
  simp only [lt_self_iff_false, ite_false, Fin.zero_lt_one, ite_true, Fin.not_lt_zero,
    mul_one, one_mul]
  rfl

theorem leviCharacter_leviOf_of_det (x : AdelicGL F (r + 1)) (z : AdelicGL F (t + 1))
    (hx : determinantNorm F (r + 1) x = 1) (hz : determinantNorm F (t + 1) z = 1) :
    leviCharacter F (blockShape r t) (leviOf x z) = 1 := by
  rw [leviCharacter_leviOf, hx, hz, one_pow, one_pow, div_one]

theorem determinantNorm_unipotentAdelic {n : ℕ} (x : RankinSelbergGlobal.unipotentAdelic F n) :
    determinantNorm F n (GeneralLinearGroupPoints.adelicEquiv F n (x : RankinSelbergGlobal.Points F n)) =
      1 :=
  determinantNorm_of_isUnitriangular (F := F) n
    (RankinSelbergGlobal.Unfolding.isUnitriangular_of_mem_unipotentAdelic F x)

theorem leviCharacter_leviOf_unipotent_mul (x : RankinSelbergGlobal.unipotentAdelic F (r + 1))
    (z : RankinSelbergGlobal.unipotentAdelic F (t + 1)) (N : FullLevi F (blockShape r t)) :
    leviCharacter F (blockShape r t)
        (leviOf (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (x : RankinSelbergGlobal.Points F (r + 1)))
          (GeneralLinearGroupPoints.adelicEquiv F (t + 1) (z : RankinSelbergGlobal.Points F (t + 1))) * N) =
      leviCharacter F (blockShape r t) N := by
  rw [map_mul, leviCharacter_leviOf_of_det _ _ (determinantNorm_unipotentAdelic x)
    (determinantNorm_unipotentAdelic z), one_mul]

theorem leviHalfCharacter_eq_of_leviCharacter_eq {M N : FullLevi F (blockShape r t)}
    (h : leviCharacter F (blockShape r t) M = leviCharacter F (blockShape r t) N) :
    ((leviHalfCharacter F (blockShape r t) M : ℂˣ) : ℂ) =
      ((leviHalfCharacter F (blockShape r t) N : ℂˣ) : ℂ) := by
  rw [coe_leviHalfCharacter, coe_leviHalfCharacter, h]

variable [CompactSpace (AdeleQuotient F)]

/-- The factor `δ_P(m)^(1/2) · H(m)^s = δ_P(m)^(1/2 + s/(r+t+2))` of the twisted section at
an adelic Levi element. -/
def levFactor (s : ℂ) (m : FullLevi F (blockShape r t)) : ℂ :=
  ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ) *
    Complex.exp (s / ((r + t + 2 : ℕ) : ℂ) *
      (Real.log ((leviCharacter F (blockShape r t) m : NNReal) : ℝ) : ℂ))

omit [CompactSpace (AdeleQuotient F)] in
theorem levFactor_unipotent_mul (s : ℂ) (x : RankinSelbergGlobal.unipotentAdelic F (r + 1))
    (z : RankinSelbergGlobal.unipotentAdelic F (t + 1)) (N : FullLevi F (blockShape r t)) :
    levFactor s (leviOf (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (x : RankinSelbergGlobal.Points F (r + 1)))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1)
        (z : RankinSelbergGlobal.Points F (t + 1))) * N) = levFactor s N := by
  have h1 := leviCharacter_leviOf_unipotent_mul x z N
  rw [levFactor, levFactor, leviHalfCharacter_eq_of_leviCharacter_eq h1, h1]

/-- The normalized Levi slice of `φ` at `k` as a finite sum of products of cusp forms. -/
def IsSliceSum (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (φ : AdelicGL F (r + t + 2) → ℂ) (k : AdelicGL F (r + t + 2)) {κ : Type*} (I : Finset κ)
    (c : κ → ℂ) (ξ₁ : κ → T.Space) (ξ₂ : κ → (dualRealization T').Space) : Prop :=
  ∀ m : FullLevi F (blockShape r t),
    ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        φ ((blockShape r t).leviEmbedding (Adeles F) m * k) =
      ∑ i ∈ I, c i *
        (ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous (ξ₁ i))
            (m (0 : Fin 2)) *
          ContinuousRationalFunctions.evaluate F (t + 1)
            ((dualRealization T').realization.toContinuous (ξ₂ i)) (m (1 : Fin 2)))

/-- The twisted section at `m k` in terms of a slice sum at `k`. -/
theorem twisted_levi_mul {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ} (s : ℂ)
    {k : AdelicGL F (r + t + 2)} (hk : k ∈ standardCompact F (r + t + 2)) {κ : Type*}
    {I : Finset κ} {c : κ → ℂ} {ξ₁ : κ → T.Space} {ξ₂ : κ → (dualRealization T').Space}
    (hslice : IsSliceSum T T' φ k I c ξ₁ ξ₂) (m : FullLevi F (blockShape r t)) :
    twisted φ s ((blockShape r t).leviEmbedding (Adeles F) m * k) =
      levFactor s m *
        ∑ i ∈ I, c i *
          (ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous (ξ₁ i))
              (m (0 : Fin 2)) *
            ContinuousRationalFunctions.evaluate F (t + 1)
              ((dualRealization T').realization.toContinuous (ξ₂ i)) (m (1 : Fin 2))) := by
  rw [twisted, heightPower_levi_mul s m k hk, ← hslice m, levFactor]
  have hne : ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

set_option maxHeartbeats 800000 in
open RankinSelbergGlobal in
/-- The global Whittaker coefficient of a finite combination of right translates of cusp forms:
if `f(u) = ∑_i d_i ξ_i(u G)` on `N(𝔸)`, then `W_f(1) = ∑_i d_i W_(ξ_i)(G)`. -/
theorem whittaker_eq_sum {n : ℕ} (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (T₂ : CuspidalOperatorRealization F n) {κ : Type*} (I : Finset κ) (d : κ → ℂ)
    (ξ : κ → T₂.Space) (G : AdelicGL F (n + 1)) (f : Points F (n + 1) → ℂ)
    (hf : ∀ u : unipotentAdelic F (n + 1), f (u : Points F (n + 1)) =
      ∑ i ∈ I, d i * ContinuousRationalFunctions.evaluate F (n + 1)
        (T₂.realization.toContinuous (ξ i))
          (GeneralLinearGroupPoints.adelicEquiv F (n + 1) (u : Points F (n + 1)) * G)) :
    generalLinearWhittakerFunction F n ψ (fun _ => 1) f 1 =
      ∑ i ∈ I, d i * cuspWhittaker F T₂ ψ (ξ i)
        ((GeneralLinearGroupPoints.adelicEquiv F (n + 1)).symm G) := by
  simp only [generalLinearWhittakerFunction, Unfolding.subgroupCharacterCoefficient_eq_integral,
    cuspWhittaker]
  have hpt : ∀ q, Unfolding.coefficientIntegrand F (Scheme F (n + 1)) (upperUnipotent F (n + 1))
      (genericCharacter F n ψ fun _ => 1) f 1 q =
      ∑ i ∈ I, d i * Unfolding.coefficientIntegrand F (Scheme F (n + 1))
        (upperUnipotent F (n + 1)) (genericCharacter F n ψ fun _ => 1)
          (cuspFunction F T₂ (ξ i)) ((GeneralLinearGroupPoints.adelicEquiv F (n + 1)).symm G) q := by
    intro q
    simp only [Unfolding.coefficientIntegrand]
    rw [mul_one, hf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : cuspFunction F T₂ (ξ i) (((Quotient.out q : unipotentAdelic F (n + 1)) :
        Points F (n + 1)) * (GeneralLinearGroupPoints.adelicEquiv F (n + 1)).symm G) =
        ContinuousRationalFunctions.evaluate F (n + 1) (T₂.realization.toContinuous (ξ i))
          (GeneralLinearGroupPoints.adelicEquiv F (n + 1)
            ((Quotient.out q : unipotentAdelic F (n + 1)) : Points F (n + 1)) * G) := by
      rw [RealPlaceWhittaker.cuspFunction_eq_evaluate,
        (GeneralLinearGroupPoints.adelicEquiv F (n + 1)).map_mul,
        MulEquiv.apply_symm_apply]
    rw [h, mul_assoc]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  · intro i _
    exact (UnramifiedWhittaker.integrable_coefficientIntegrand F ψ hψ T₂ (ξ i) _).const_mul _

omit [CompactSpace (AdeleQuotient F)] in
theorem leviPair_mul_levi (x : AdelicGL F (r + 1)) (z : AdelicGL F (t + 1))
    (N : FullLevi F (blockShape r t)) :
    leviPair F r t x z * (blockShape r t).leviEmbedding (Adeles F) N =
      (blockShape r t).leviEmbedding (Adeles F) (leviOf x z * N) := by
  rw [leviPair_eq_leviEmbedding, (blockShape r t).leviEmbedding (Adeles F) |>.map_mul]

/-- The first block of an adelic Levi element. -/
abbrev leviFst (N : FullLevi F (blockShape r t)) : AdelicGL F (r + 1) := N (0 : Fin 2)

/-- The second block of an adelic Levi element. -/
abbrev leviSnd (N : FullLevi F (blockShape r t)) : AdelicGL F (t + 1) := N (1 : Fin 2)

set_option maxHeartbeats 800000 in
open RankinSelbergGlobal in
/-- **The Levi Whittaker coefficient at a Levi element.** If the normalized Levi slice of `φ`
at `k` is `∑_i c_i ξ₁ᵢ ⊗ ξ₂ᵢ`, then `W_M(φ_s)(m k) = δ_P(m)^(1/2 + s/(r+t+2)) ·
∑_i c_i W_(ξ₁ᵢ)(m₁) W_(ξ₂ᵢ)(m₂)` for every adelic Levi element `m = diag(m₁, m₂)`. -/
theorem leviWhittaker_levi_mul (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    {φ : AdelicGL F (r + t + 2) → ℂ} (s : ℂ) {k : AdelicGL F (r + t + 2)}
    (hk : k ∈ standardCompact F (r + t + 2)) {κ : Type*} {I : Finset κ} {c : κ → ℂ}
    {ξ₁ : κ → T.Space} {ξ₂ : κ → (dualRealization T').Space}
    (hslice : IsSliceSum T T' φ k I c ξ₁ ξ₂) (N : FullLevi F (blockShape r t)) :
    leviWhittaker F r t ψ (twisted φ s) ((blockShape r t).leviEmbedding (Adeles F) N * k) =
      levFactor s N *
        ∑ i ∈ I, c i *
          (cuspWhittaker F T ψ (ξ₁ i)
              ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (leviFst N)) *
            cuspWhittaker F (dualRealization T') ψ (ξ₂ i)
              ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd N))) := by
  have hinner : ∀ u₁ : unipotentAdelic F (r + 1),
      generalLinearWhittakerFunction F t ψ (fun _ => 1)
          (fun y => twisted φ s (leviPair F r t
            (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (u₁ : Points F (r + 1)))
            (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) *
              ((blockShape r t).leviEmbedding (Adeles F) N * k))) 1 =
        ∑ i ∈ I, (levFactor s N * c i * cuspWhittaker F (dualRealization T') ψ (ξ₂ i)
              ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd N))) *
          ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous (ξ₁ i))
            (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (u₁ : Points F (r + 1)) *
              leviFst N) := by
    intro u₁
    rw [whittaker_eq_sum ψ hψ (dualRealization T') I
      (fun i => levFactor s N * c i * ContinuousRationalFunctions.evaluate F (r + 1)
        (T.realization.toContinuous (ξ₁ i))
          (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (u₁ : Points F (r + 1)) *
            leviFst N)) ξ₂ (leviSnd N)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact mul_right_comm _ _ _
    · intro u₂
      rw [← mul_assoc, leviPair_mul_levi, twisted_levi_mul s hk hslice,
        levFactor_unipotent_mul s u₁ u₂ N, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change levFactor s N * (c i * (ContinuousRationalFunctions.evaluate F (r + 1)
          (T.realization.toContinuous (ξ₁ i))
            (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (u₁ : Points F (r + 1)) *
              leviFst N) *
        ContinuousRationalFunctions.evaluate F (t + 1)
          ((dualRealization T').realization.toContinuous (ξ₂ i))
            (GeneralLinearGroupPoints.adelicEquiv F (t + 1) (u₂ : Points F (t + 1)) *
              leviSnd N))) = _
      simp only [mul_assoc]
  unfold leviWhittaker
  rw [whittaker_eq_sum ψ hψ T I _ ξ₁ (leviFst N) _ hinner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize cuspWhittaker F (dualRealization T') ψ (ξ₂ i)
    ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd N)) = w₂
  generalize cuspWhittaker F T ψ (ξ₁ i)
    ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (leviFst N)) = w₁
  generalize levFactor s N = L
  ring

omit [CompactSpace (AdeleQuotient F)] in
theorem levFactor_mul (s : ℂ) (M N : FullLevi F (blockShape r t)) :
    levFactor s (M * N) = levFactor s M * levFactor s N := by
  have hM : (0 : ℝ) < ((leviCharacter F (blockShape r t) M : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hN : (0 : ℝ) < ((leviCharacter F (blockShape r t) N : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  simp only [levFactor, map_mul, Units.val_mul, NNReal.coe_mul]
  rw [Real.log_mul hM.ne' hN.ne', Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

omit [CompactSpace (AdeleQuotient F)] in
/-- A parabolic element is its unipotent part times its Levi part. -/
theorem parabolic_eq_unipotent_mul_levi (p : Full F (blockShape r t)) :
    p.val = (((blockShape r t).unipotentPart (Adeles F) p : (blockShape r t).parabolic (Adeles F)) :
        AdelicGL F (r + t + 2)) *
      (blockShape r t).leviEmbedding (Adeles F) ((blockShape r t).leviProjection (Adeles F) p) := by
  change p.val = (p * ((blockShape r t).leviInParabolic (Adeles F)
      ((blockShape r t).leviProjection (Adeles F) p))⁻¹).val *
    ((blockShape r t).leviInParabolic (Adeles F) ((blockShape r t).leviProjection (Adeles F) p)).val
  rw [← Subgroup.coe_mul, inv_mul_cancel_right]

omit [CompactSpace (AdeleQuotient F)] in
theorem unipotentPart_mem (p : Full F (blockShape r t)) :
    (((blockShape r t).unipotentPart (Adeles F) p : (blockShape r t).parabolic (Adeles F)) :
        AdelicGL F (r + t + 2)) ∈ (blockShape r t).unipotentSubgroup (Adeles F) :=
  ⟨_, ((blockShape r t).unipotentPart (Adeles F) p).property, rfl⟩

omit [CompactSpace (AdeleQuotient F)] in
theorem levi_conj_mem (Q : FullLevi F (blockShape r t)) (n : AdelicGL F (r + t + 2))
    (hn : n ∈ (blockShape r t).unipotentSubgroup (Adeles F)) :
    (blockShape r t).leviEmbedding (Adeles F) Q * n *
        ((blockShape r t).leviEmbedding (Adeles F) Q)⁻¹ ∈
      (blockShape r t).unipotentSubgroup (Adeles F) := by
  obtain ⟨h, hh, rfl⟩ := hn
  set q := (blockShape r t).leviInParabolic (Adeles F) Q
  refine ⟨q * h * q⁻¹, ((blockShape r t).unipotentRadicalNormal (Adeles F)).conj_mem h hh q, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

/-- The Levi Whittaker coefficient at `m p k`, for `p` parabolic, only sees the Levi part of
`p`. -/
theorem leviWhittaker_levi_mul_parabolic {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}
    (hφ : IsSection T T' φ) (ψ : AddChar (Adeles F) ℂ) (s : ℂ) (Q : FullLevi F (blockShape r t))
    (p : Full F (blockShape r t)) (k : AdelicGL F (r + t + 2)) :
    leviWhittaker F r t ψ (twisted φ s)
        ((blockShape r t).leviEmbedding (Adeles F) Q * (p.val * k)) =
      leviWhittaker F r t ψ (twisted φ s)
        ((blockShape r t).leviEmbedding (Adeles F)
          (Q * (blockShape r t).leviProjection (Adeles F) p) * k) := by
  set u := (((blockShape r t).unipotentPart (Adeles F) p : (blockShape r t).parabolic (Adeles F)) :
    AdelicGL F (r + t + 2))
  have e : (blockShape r t).leviEmbedding (Adeles F) Q * (p.val * k) =
      ((blockShape r t).leviEmbedding (Adeles F) Q * u *
        ((blockShape r t).leviEmbedding (Adeles F) Q)⁻¹) *
      ((blockShape r t).leviEmbedding (Adeles F)
        (Q * (blockShape r t).leviProjection (Adeles F) p) * k) := by
    rw [parabolic_eq_unipotent_mul_levi p, map_mul]
    group
    rfl
  rw [e, leviWhittaker_unipotent_mul ψ _ (twisted_unipotent_mul hφ s) _ _
    (levi_conj_mem Q u (unipotentPart_mem p))]

open RankinSelbergGlobal ClassFieldTheory.Global.RelativeWeilGroup in
/-- **One-place factorization of a cusp Whittaker function at an integral point.** For a vector
spherical outside `S`, a finite place `v ∉ S` and a point `g` whose component at `v` is
integral, `W_x(ι_v(h) g) = W°(h) W_x(g)`. -/
theorem cuspWhittaker_localPoint_mul {n : ℕ}
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (T₂ : CuspidalOperatorRealization F n) (P₂ : CuspidalSpectralPresentation.{u, uQ} T₂)
    (S : Finset (FinitePlace F)) (hP : P₂.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (x : T₂.Space) (hx : RankinSelbergGlobal.IsSphericalOutside F T₂ S x)
    (v : FinitePlace F) (hv : v ∉ S)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (ϖ : (CompletionPadic.padicField v).Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) ϖ)
    (hθ : GeneralLinear.Iwasawa.IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel)
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n))
    (a : Fin (n + 1) → ℂˣ)
    (ha : Unramified.Eigenvalues.ofTuple a =
      P₂.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (g : Points F (n + 1))
    (hg : finiteComponent F (n + 1) v g ∈ FiniteAdelicGL.localIntegral F (n + 1) v)
    (h : FiniteLocalGL F (n + 1) v) :
    cuspWhittaker F T₂ ψ.complex x (localPoint F (n + 1) v h * g) =
      GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _
            (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n)
          (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a h *
        cuspWhittaker F T₂ ψ.complex x g := by
  have hfac := UnramifiedWhittaker.unramifiedWhittakerFactorization.{u, uQ} F ψ hψF n T₂ P₂ S hP
    hS x hx v hv ψv hψv ϖ hϖ a ha
  set gv := finiteComponent F (n + 1) v g with hgv
  set g' := g * (localPoint F (n + 1) v gv)⁻¹ with hg'def
  have hg' : finiteComponent F (n + 1) v g' = 1 :=
    LocalPointFactorization.finiteComponent_mul_inv_localPoint F (n + 1) v g
  have hgK := UnequalEulerFactorization.mem_integralSubgroup_of_mem_localIntegral v hg
  have e1 := (hfac g' hg' (h * gv)).1
  have e2 := (hfac g' hg' gv).1
  have hW1 : GeneralLinear.Spherical.sphericalWhittaker hϖ
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n)
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a (h * gv) =
      GeneralLinear.Spherical.sphericalWhittaker hϖ
        (@Whittaker.standardCharacter _ _
          (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n)
        (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a h :=
    GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ _ hθ h hgK
  have hW2 : GeneralLinear.Spherical.sphericalWhittaker hϖ
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv n)
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a gv = 1 := by
    have := GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ
      (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a hθ 1 hgK
    rw [one_mul] at this
    rw [this, GeneralLinear.Spherical.sphericalWhittaker_one hϖ _ _ hθ]
  have hgg : g = g' * localPoint F (n + 1) v gv := by rw [hg'def, inv_mul_cancel_right]
  rw [LocalPointFactorization.localPoint_mul_eq F (n + 1) v h g, ← hgv, ← hg'def]
  change cuspWhittaker F T₂ ψ.complex x (g' * (GeneralLinearGroupPoints.adelicEquiv F (n + 1)).symm
    (AdelicGL.ofFinite F (n + 1) (FiniteAdelicGL.localInclusion F (n + 1) v (h * gv)))) = _
  rw [e1, hW1]
  conv_rhs => rw [hgg]
  change _ = _ * cuspWhittaker F T₂ ψ.complex x (g' * (GeneralLinearGroupPoints.adelicEquiv F (n + 1)).symm
    (AdelicGL.ofFinite F (n + 1) (FiniteAdelicGL.localInclusion F (n + 1) v gv)))
  rw [e2, hW2, mul_one, mul_comm]

omit [CompactSpace (AdeleQuotient F)] in
variable (F) in
/-- The component at a finite place `v` of an adelic matrix. -/
def comp (n : ℕ) (v : FinitePlace F) : AdelicGL F n →* FiniteLocalGL F n v :=
  (FiniteAdelicGL.localProjection F n v).toMonoidHom.comp (AdelicGL.finite F n).toMonoidHom

omit [CompactSpace (AdeleQuotient F)] in
theorem comp_apply {n : ℕ} (v : FinitePlace F) (g : AdelicGL F n) (i j : Fin n) :
    comp F n v g i j = (g i j).2 v :=
  rfl

omit [CompactSpace (AdeleQuotient F)] in
/-- The Levi blocks at `v` of a parabolic element integral at `v` are integral. -/
theorem comp_leviFst_mem (v : FinitePlace F) (p : Full F (blockShape r t))
    (hp : comp F (r + t + 2) v p.val ∈ FiniteAdelicGL.localIntegral F (r + t + 2) v) :
    comp F (r + 1) v (leviFst ((blockShape r t).leviProjection (Adeles F) p)) ∈
      FiniteAdelicGL.localIntegral F (r + 1) v := by
  rw [FiniteAdelicGL.mem_localIntegral] at hp ⊢
  have hinv : ((comp F (r + 1) v (leviFst ((blockShape r t).leviProjection (Adeles F) p)))⁻¹) =
      comp F (r + 1) v (leviFst ((blockShape r t).leviProjection (Adeles F) p⁻¹)) := by
    rw [← map_inv, map_inv]
    rfl
  refine ⟨fun a b => hp.1 _ _, fun a b => ?_⟩
  rw [hinv]
  have h := hp.2 ((blockShape r t).index (0 : Fin 2) a) ((blockShape r t).index (0 : Fin 2) b)
  rw [← map_inv] at h
  exact h

omit [CompactSpace (AdeleQuotient F)] in
theorem comp_leviSnd_mem (v : FinitePlace F) (p : Full F (blockShape r t))
    (hp : comp F (r + t + 2) v p.val ∈ FiniteAdelicGL.localIntegral F (r + t + 2) v) :
    comp F (t + 1) v (leviSnd ((blockShape r t).leviProjection (Adeles F) p)) ∈
      FiniteAdelicGL.localIntegral F (t + 1) v := by
  rw [FiniteAdelicGL.mem_localIntegral] at hp ⊢
  have hinv : ((comp F (t + 1) v (leviSnd ((blockShape r t).leviProjection (Adeles F) p)))⁻¹) =
      comp F (t + 1) v (leviSnd ((blockShape r t).leviProjection (Adeles F) p⁻¹)) := by
    rw [← map_inv, map_inv]
    rfl
  refine ⟨fun a b => hp.1 _ _, fun a b => ?_⟩
  rw [hinv]
  have h := hp.2 ((blockShape r t).index (1 : Fin 2) a) ((blockShape r t).index (1 : Fin 2) b)
  rw [← map_inv] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- A section built from cusp forms spherical outside `S` has, at every `k` of the standard
maximal compact subgroup, a slice sum with vectors spherical outside `S`. -/
theorem exists_isSliceSum {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} {S : Finset (FinitePlace F)}
    {φ : AdelicGL F (r + t + 2) → ℂ} (hsph : IsSphericalSectionOutside T T' S φ)
    (k : AdelicGL F (r + t + 2)) (hk : k ∈ standardCompact F (r + t + 2)) :
    ∃ (I : Finset ({x : T.Space // RankinSelbergGlobal.IsSphericalOutside F T S x} ×
        {y : (dualRealization T').Space //
          RankinSelbergGlobal.IsSphericalOutside F (dualRealization T') S y}))
      (c : {x : T.Space // RankinSelbergGlobal.IsSphericalOutside F T S x} ×
        {y : (dualRealization T').Space //
          RankinSelbergGlobal.IsSphericalOutside F (dualRealization T') S y} → ℂ),
      IsSliceSum T T' φ k I c (fun i => i.1.1) (fun i => i.2.1) := by
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (R := ℂ)).mp (hsph.2 ⟨k, hk⟩)
  refine ⟨c.support, c, fun m => ?_⟩
  have h := congrFun hc m
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

omit [CompactSpace (AdeleQuotient F)] in
variable (F r t) in
/-- The adelic Levi element with components `m₁`, `m₂` at the finite place `v` and `1`
elsewhere. -/
abbrev localLevi (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) : FullLevi F (blockShape r t) :=
  leviOf (AdelicGL.ofFinite F (r + 1) (FiniteAdelicGL.localInclusion F (r + 1) v m₁))
    (AdelicGL.ofFinite F (t + 1) (FiniteAdelicGL.localInclusion F (t + 1) v m₂))

omit [CompactSpace (AdeleQuotient F)] in
/-- The adelic determinant norm of a matrix supported at `v` is the normalized local norm of
its determinant. -/
theorem determinantNorm_localInclusion (n : ℕ) (v : FinitePlace F) (m : FiniteLocalGL F n v) :
    ((determinantNorm F n (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v m)) :
        NNReal) : ℝ) =
      (((CompletionPadic.padicField v).canonicalTopologicalData.determinantNorm n m : NNReal) :
        ℝ) := by
  rw [AdelicBlockDeterminantCharacter.coe_determinantNorm_localInclusion,
    PadicField.TopologicalData.determinantNorm_coe,
    RankinSelbergGlobal.DeterminantProducts.normalizedAbs_eq_completion_norm]

omit [CompactSpace (AdeleQuotient F)] in
theorem leviCharacter_localLevi (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) :
    ((leviCharacter F (blockShape r t) (localLevi F r t v m₁ m₂) : NNReal) : ℝ) =
      Shahidi.twoBlockModulus (CompletionPadic.padicField v) m₁ m₂ := by
  rw [leviCharacter_leviOf, Units.val_div_eq_div_val, NNReal.coe_div, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, NNReal.coe_pow, NNReal.coe_pow, determinantNorm_localInclusion,
    determinantNorm_localInclusion]
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem twoBlockModulus_pos (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) :
    0 < Shahidi.twoBlockModulus (CompletionPadic.padicField v) m₁ m₂ := by
  unfold Shahidi.twoBlockModulus
  exact div_pos (pow_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _)
    (pow_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _)

omit [CompactSpace (AdeleQuotient F)] in
/-- The factor `δ_P^(1/2) H^s` at a Levi element supported at `v` is the local power
`δ_P(m₁, m₂)^(1/2 + s/(r+t+2))`. -/
theorem levFactor_localLevi (s : ℂ) (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) :
    levFactor s (localLevi F r t v m₁ m₂) =
      ((Shahidi.twoBlockModulus (CompletionPadic.padicField v) m₁ m₂ : ℝ) : ℂ) ^
        ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) := by
  have hδ := twoBlockModulus_pos v m₁ m₂
  simp only [levFactor, coe_leviHalfCharacter, Real.coe_sqrt]
  rw [leviCharacter_localLevi]
  set δ := Shahidi.twoBlockModulus (CompletionPadic.padicField v) m₁ m₂
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hδ.ne'),
    ← Complex.ofReal_log hδ.le, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hδ,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [CompactSpace (AdeleQuotient F)] in
theorem comp_mem_localIntegral_of_mem_standardCompact {n : ℕ} (v : FinitePlace F)
    {k : AdelicGL F n} (hk : k ∈ standardCompact F n) :
    comp F n v k ∈ FiniteAdelicGL.localIntegral F n v :=
  (FiniteAdelicGL.mem_standardIntegral_iff_local F n _).mp hk.2 v

omit [CompactSpace (AdeleQuotient F)] in
theorem finiteComponent_symm (n : ℕ) (v : FinitePlace F) (X : AdelicGL F n) :
    RankinSelbergGlobal.finiteComponent F n v ((GeneralLinearGroupPoints.adelicEquiv F n).symm X) =
      comp F n v X := by
  simp only [RankinSelbergGlobal.finiteComponent, MulEquiv.apply_symm_apply]
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem alg_aux₁ (c A B x₁ x₂ : ℂ) : c * (A * x₁ * (B * x₂)) = A * B * (c * (x₁ * x₂)) := by
  ring

omit [CompactSpace (AdeleQuotient F)] in
theorem alg_aux₂ (D L A B X : ℂ) : D * L * (A * B * X) = D * A * B * (L * X) := by
  ring

omit [CompactSpace (AdeleQuotient F)] in
theorem symm_leviFst_localLevi_mul (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) (M : FullLevi F (blockShape r t)) :
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (leviFst (localLevi F r t v m₁ m₂ * M)) =
      RankinSelbergGlobal.localPoint F (r + 1) v m₁ *
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (leviFst M) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm.map_mul _ _

omit [CompactSpace (AdeleQuotient F)] in
theorem symm_leviSnd_localLevi_mul (v : FinitePlace F) (m₁ : FiniteLocalGL F (r + 1) v)
    (m₂ : FiniteLocalGL F (t + 1) v) (M : FullLevi F (blockShape r t)) :
    (GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd (localLevi F r t v m₁ m₂ * M)) =
      RankinSelbergGlobal.localPoint F (t + 1) v m₂ *
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd M) :=
  (GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm.map_mul _ _

set_option maxHeartbeats 1600000 in
open RankinSelbergGlobal ClassFieldTheory.Global.RelativeWeilGroup in
/-- **The Levi Whittaker coefficient under a Levi element at an unramified place.** For a
section built from cusp forms spherical outside `S`, a finite place `v ∉ S`, a point `g`
integral at `v` and local Levi blocks `m₁`, `m₂`,
`W_M(φ_s)(ι_v(diag(m₁, m₂)) g) = δ_P(m₁, m₂)^(1/2 + s/(r+t+2)) W°(m₁; a) W°(m₂; c) W_M(φ_s)(g)`,
where `a` and `c` are the Satake tuples of `P` and `Pd` at `v`. -/
theorem leviWhittaker_localLevi_mul
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (Pd : CuspidalSpectralPresentation.{u, uQ} (dualRealization T'))
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {φ : AdelicGL F (r + t + 2) → ℂ} (hφ : IsSection T T' φ)
    (hsph : IsSphericalSectionOutside T T' S φ) (s : ℂ) (v : FinitePlace F) (hv : v ∉ S)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (ϖ : (CompletionPadic.padicField v).Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) ϖ)
    (hθ₁ : GeneralLinear.Iwasawa.IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel)
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r))
    (hθ₂ : GeneralLinear.Iwasawa.IsIntegrallyTrivial
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel)
      (@Whittaker.standardCharacter _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv t))
    (a : Fin (r + 1) → ℂˣ)
    (ha : Unramified.Eigenvalues.ofTuple a =
      P.spectralSystem.eigenvalues v (fun hvP => hv (hP hvP)))
    (c : Fin (t + 1) → ℂˣ)
    (hc : Unramified.Eigenvalues.ofTuple c =
      Pd.spectralSystem.eigenvalues v (fun hvP => hv (hPd hvP)))
    (g : AdelicGL F (r + t + 2))
    (hg : comp F (r + t + 2) v g ∈ FiniteAdelicGL.localIntegral F (r + t + 2) v)
    (m₁ : FiniteLocalGL F (r + 1) v) (m₂ : FiniteLocalGL F (t + 1) v) :
    leviWhittaker F r t ψ.complex (twisted φ s)
        ((blockShape r t).leviEmbedding (Adeles F) (localLevi F r t v m₁ m₂) * g) =
      Shahidi.UnramifiedSection.leviValue hϖ ψv a c s m₁ m₂ *
        leviWhittaker F r t ψ.complex (twisted φ s) g := by
  have hstd := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψF
  obtain ⟨p, k, hk, hpk⟩ := exists_parabolic_factor' F r t g
  have hp : comp F (r + t + 2) v p.val ∈ FiniteAdelicGL.localIntegral F (r + t + 2) v := by
    have e : p.val = g * k⁻¹ := by rw [← hpk, mul_inv_cancel_right]
    rw [e, map_mul, map_inv]
    exact mul_mem hg (inv_mem (comp_mem_localIntegral_of_mem_standardCompact v hk))
  obtain ⟨I, cc, hslice⟩ := exists_isSliceSum hsph k hk
  set M' := (blockShape r t).leviProjection (Adeles F) p with hM'
  have e1 : leviWhittaker F r t ψ.complex (twisted φ s)
      ((blockShape r t).leviEmbedding (Adeles F) (localLevi F r t v m₁ m₂) * g) =
      leviWhittaker F r t ψ.complex (twisted φ s)
        ((blockShape r t).leviEmbedding (Adeles F) (localLevi F r t v m₁ m₂ * M') * k) := by
    have h := leviWhittaker_levi_mul_parabolic hφ ψ.complex s (localLevi F r t v m₁ m₂) p k
    rwa [hpk] at h
  have e1' : leviWhittaker F r t ψ.complex (twisted φ s) g =
      leviWhittaker F r t ψ.complex (twisted φ s)
        ((blockShape r t).leviEmbedding (Adeles F) M' * k) := by
    have h := leviWhittaker_levi_mul_parabolic hφ ψ.complex s 1 p k
    rwa [map_one, one_mul, one_mul, hpk] at h
  have h1 := comp_leviFst_mem v p hp
  have h2 := comp_leviSnd_mem v p hp
  have hW : ∀ i ∈ I,
      cc i * (cuspWhittaker F T ψ.complex i.1.1
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
            (leviFst (localLevi F r t v m₁ m₂ * M'))) *
        cuspWhittaker F (dualRealization T') ψ.complex i.2.1
          ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm
            (leviSnd (localLevi F r t v m₁ m₂ * M')))) =
      (GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _
            (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r)
          (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a m₁ *
        GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _
            (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv t)
          (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality c m₂) *
      (cc i * (cuspWhittaker F T ψ.complex i.1.1
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (leviFst M')) *
        cuspWhittaker F (dualRealization T') ψ.complex i.2.1
          ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd M')))) := by
    intro i _
    have w1 := (congrArg (cuspWhittaker F T ψ.complex i.1.1)
      (symm_leviFst_localLevi_mul v m₁ m₂ M')).trans
      (cuspWhittaker_localPoint_mul ψ hψF T P S hP hS i.1.1 i.1.2 v hv ψv hψv ϖ hϖ hθ₁ a ha _
        (by rw [finiteComponent_symm]; exact h1) m₁)
    have w2 := (congrArg (cuspWhittaker F (dualRealization T') ψ.complex i.2.1)
      (symm_leviSnd_localLevi_mul v m₁ m₂ M')).trans
      (cuspWhittaker_localPoint_mul ψ hψF (dualRealization T') Pd S hPd hS i.2.1 i.2.2 v hv ψv
        hψv ϖ hϖ hθ₂ c hc _ (by rw [finiteComponent_symm]; exact h2) m₂)
    rewrite [w1, w2]
    exact alg_aux₁ _ _ _ _ _
  have hsum : (∑ i ∈ I,
      cc i * (cuspWhittaker F T ψ.complex i.1.1
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
            (leviFst (localLevi F r t v m₁ m₂ * M'))) *
        cuspWhittaker F (dualRealization T') ψ.complex i.2.1
          ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm
            (leviSnd (localLevi F r t v m₁ m₂ * M'))))) =
      (GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _
            (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv r)
          (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality a m₁ *
        GeneralLinear.Spherical.sphericalWhittaker hϖ
          (@Whittaker.standardCharacter _ _
            (CompletionPadic.padicField v).canonicalTopologicalData.topology ψv t)
          (CompletionPadic.padicField v).canonicalTopologicalData.residueCardinality c m₂) *
      ∑ i ∈ I, cc i * (cuspWhittaker F T ψ.complex i.1.1
          ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (leviFst M')) *
        cuspWhittaker F (dualRealization T') ψ.complex i.2.1
          ((GeneralLinearGroupPoints.adelicEquiv F (t + 1)).symm (leviSnd M'))) := by
    exact (Finset.sum_congr rfl hW).trans (Finset.mul_sum _ _ _).symm
  have hlev : levFactor s (localLevi F r t v m₁ m₂ * M') =
      ((Shahidi.twoBlockModulus (CompletionPadic.padicField v) m₁ m₂ : ℝ) : ℂ) ^
        ((1 : ℂ) / 2 + s / ((r + t + 2 : ℕ) : ℂ)) * levFactor s M' := by
    rw [levFactor_mul, levFactor_localLevi]
  refine e1.trans ((leviWhittaker_levi_mul ψ.complex hstd s hk hslice _).trans ?_)
  refine Eq.trans (congrArg₂ (· * ·) hlev hsum) ?_
  refine Eq.trans (alg_aux₂ _ _ _ _ _) ?_
  exact congrArg (fun z => Shahidi.UnramifiedSection.leviValue hϖ ψv a c s m₁ m₂ * z)
    (e1'.trans (leviWhittaker_levi_mul ψ.complex hstd s hk hslice M')).symm
end Langlands.Global.CuspidalPairEisenstein.Oneplace
