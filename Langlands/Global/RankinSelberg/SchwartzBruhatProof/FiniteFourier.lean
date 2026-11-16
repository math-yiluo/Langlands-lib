import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Duality

/-! # Fourier analysis of coset indicators on a totally disconnected group

Let `G` be a commutative topological group with a translation-invariant measure `ν`, and
let `p : G → G → ℂ` be a symmetric pairing which is a unitary character in each variable.
The transform `F f(η) = ∫ f(u) p(u, η) dν(u)` sends the indicator of a coset `a + H` of a
compact open subgroup `H` to `ν(H) p(a, ·) 1_(H')`, where `H'` is the annihilator of `H`.
If the annihilator of `H'` is `H` again, `F F f(x) = ν(H) ν(H') f(-x)` for every compactly
supported `H`-invariant `f`, and `F f` is locally constant and supported in `H'`.

We then specialise to `𝔸_f^n`, its lattices `L_m^n`, an additive Haar measure and the pairing
`(u, η) ↦ ψ_f(∑_j u_j η_j)`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Topology
open Langlands.Global.CompletionPadic
open Langlands.Global.RankinSelbergGlobal.EqualAnalytic (finiteCharacter finiteCharacter_add
  norm_finiteCharacter)
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

section Generic

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- A symmetric pairing which is a unitary character in each variable, continuous in the first
and locally constant in the second. -/
structure IsFinitePairing (p : G → G → ℂ) : Prop where
  add_left : ∀ u u' η, p (u + u') η = p u η * p u' η
  symm : ∀ u η, p u η = p η u
  norm_eq : ∀ u η, ‖p u η‖ = 1
  continuous_left : ∀ η, Continuous fun u => p u η
  isLocallyConstant_right : ∀ u, IsLocallyConstant (p u)

namespace IsFinitePairing

variable {p : G → G → ℂ}

omit [IsTopologicalAddGroup G] in
theorem add_right (hp : IsFinitePairing p) (u η η' : G) :
    p u (η + η') = p u η * p u η' := by
  rw [hp.symm, hp.add_left, hp.symm η, hp.symm η']

omit [IsTopologicalAddGroup G] in
theorem ne_zero (hp : IsFinitePairing p) (u η : G) : p u η ≠ 0 := by
  intro h
  have := hp.norm_eq u η
  rw [h, norm_zero] at this
  exact zero_ne_one this

omit [IsTopologicalAddGroup G] in
theorem zero_left (hp : IsFinitePairing p) (η : G) : p 0 η = 1 := by
  have h := hp.add_left 0 0 η
  rw [add_zero] at h
  exact mul_left_cancel₀ (hp.ne_zero 0 η) (h.symm.trans (mul_one _).symm)

end IsFinitePairing

omit [AddCommGroup G] [IsTopologicalAddGroup G] in
theorem isLocallyConstant_finset_sum {ι : Type*} (s : Finset ι) (g : ι → G → ℂ)
    (h : ∀ i ∈ s, IsLocallyConstant (g i)) : IsLocallyConstant fun x => ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddLeftInvariant]
  (p : G → G → ℂ)

/-- The transform `F f(η) = ∫ f(u) p(u, η) dν(u)`. -/
def finFourier (f : G → ℂ) (η : G) : ℂ := ∫ u, f u * p u η ∂ν

variable {ν p}

theorem integral_cosetIndicator_mul_eq (hp : IsFinitePairing p) (H : AddSubgroup G) (a η : G) :
    ∫ u, cosetIndicator H a u * p u η ∂ν =
      p a η * ∫ w, (H : Set G).indicator (fun w => p w η) w ∂ν := by
  rw [← integral_add_right_eq_self (μ := ν) (fun u => cosetIndicator H a u * p u η) a,
    ← integral_const_mul]
  congr 1
  funext w
  by_cases hwH : w ∈ H
  · have h1 : cosetIndicator H a (w + a) = 1 := by simp [cosetIndicator, hwH]
    rw [h1, Set.indicator_of_mem (show w ∈ (H : Set G) from hwH), hp.add_left]
    ring
  · have h0 : cosetIndicator H a (w + a) = 0 := by simp [cosetIndicator, hwH]
    rw [h0, Set.indicator_of_notMem (show w ∉ (H : Set G) from hwH), zero_mul, mul_zero]

/-- The integral of a coset indicator against a character trivial on the subgroup. -/
theorem integral_cosetIndicator_mul_of_forall (hp : IsFinitePairing p) (H : AddSubgroup G)
    (hHo : IsOpen (H : Set G)) (a η : G) (hall : ∀ h ∈ H, p h η = 1) :
    ∫ u, cosetIndicator H a u * p u η ∂ν = ν.real H * p a η := by
  rw [integral_cosetIndicator_mul_eq hp,
    Set.indicator_congr (g := fun _ => (1 : ℂ)) (fun w hw => hall w hw),
    integral_indicator_const _ hHo.measurableSet]
  simp only [Complex.real_smul, mul_one]
  ring

/-- The integral of a coset indicator against a character nontrivial on the subgroup. -/
theorem integral_cosetIndicator_mul_of_exists (hp : IsFinitePairing p) (H : AddSubgroup G)
    (a η : G) {h₀ : G} (hh₀ : h₀ ∈ H) (hne : p h₀ η ≠ 1) :
    ∫ u, cosetIndicator H a u * p u η ∂ν = 0 := by
  rw [integral_cosetIndicator_mul_eq hp]
  set I := ∫ w, (H : Set G).indicator (fun w => p w η) w ∂ν with hI
  have hshift : I = p h₀ η * I := by
    have h2 : (fun w => (H : Set G).indicator (fun w => p w η) (w + h₀)) =
        fun w => p h₀ η * (H : Set G).indicator (fun w => p w η) w := by
      funext w
      have hiff : w + h₀ ∈ H ↔ w ∈ H := H.add_mem_cancel_right hh₀
      by_cases hwH : w ∈ H
      · rw [Set.indicator_of_mem (show w + h₀ ∈ (H : Set G) from hiff.mpr hwH),
          Set.indicator_of_mem (show w ∈ (H : Set G) from hwH), hp.add_left]
        ring
      · rw [Set.indicator_of_notMem (show w + h₀ ∉ (H : Set G) from mt hiff.mp hwH),
          Set.indicator_of_notMem (show w ∉ (H : Set G) from hwH), mul_zero]
    have h1 : ∫ w, (H : Set G).indicator (fun w => p w η) (w + h₀) ∂ν = I :=
      integral_add_right_eq_self _ h₀
    rw [h2, integral_const_mul] at h1
    exact h1.symm
  have : (1 - p h₀ η) * I = 0 := by rw [sub_mul, one_mul, ← hshift, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · rw [h, mul_zero]

/-- `F(1_(a + H)) = ν(H) p(a, ·) 1_(H')` when `H'` is the annihilator of `H`. -/
theorem finFourier_cosetIndicator (hp : IsFinitePairing p) (H H' : AddSubgroup G)
    (hHo : IsOpen (H : Set G)) (hann : ∀ η, (∀ h ∈ H, p h η = 1) ↔ η ∈ H') (a η : G) :
    finFourier ν p (cosetIndicator H a) η = ν.real H * p a η * cosetIndicator H' 0 η := by
  unfold finFourier
  by_cases hη : η ∈ H'
  · rw [integral_cosetIndicator_mul_of_forall hp H hHo a η ((hann η).mpr hη)]
    simp [cosetIndicator, hη]
  · have : ¬ ∀ h ∈ H, p h η = 1 := fun h => hη ((hann η).mp h)
    push Not at this
    obtain ⟨h₀, hh₀, hne⟩ := this
    rw [integral_cosetIndicator_mul_of_exists hp H a η hh₀ hne]
    simp [cosetIndicator, hη]

variable [IsFiniteMeasureOnCompacts ν]

omit [ν.IsAddLeftInvariant] in
theorem integrable_cosetIndicator_mul (hp : IsFinitePairing p) (H : AddSubgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) (a η : G) :
    Integrable (fun u => cosetIndicator H a u * p u η) ν :=
  ((isLocallyConstant_cosetIndicator H hHo a).continuous.mul
    (hp.continuous_left η)).integrable_of_hasCompactSupport
    (hasCompactSupport_cosetIndicator H hHo hHc a).mul_right

/-- **Finite Fourier inversion.** If `H` and `H'` are compact open subgroups, each the
annihilator of the other, then for every compactly supported `H`-invariant `f` the transform
`F f` is locally constant with compact support and `F F f(x) = ν(H) ν(H') f(-x)`. -/
theorem finFourier_finFourier (hp : IsFinitePairing p) (H H' : AddSubgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G))
    (hH'o : IsOpen (H' : Set G)) (hH'c : IsCompact (H' : Set G))
    (hann : ∀ η, (∀ h ∈ H, p h η = 1) ↔ η ∈ H')
    (hann' : ∀ x, (∀ h ∈ H', p h x = 1) ↔ x ∈ H)
    {f : G → ℂ} (hf : HasCompactSupport f) (hinv : ∀ x, ∀ h ∈ H, f (x + h) = f x) :
    (IsLocallyConstant (finFourier ν p f) ∧ HasCompactSupport (finFourier ν p f)) ∧
      ∀ x, finFourier ν p (finFourier ν p f) x = ν.real H * ν.real H' * f (-x) := by
  obtain ⟨s, hs⟩ := exists_eq_sum_cosetIndicator H hHo hf hinv
  have hFf : finFourier ν p f =
      fun η => ∑ a ∈ s, f a * (ν.real H * p a η * cosetIndicator H' 0 η) := by
    funext η
    rw [congrArg (fun g => finFourier ν p g η) hs]
    unfold finFourier
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun a _ =>
      (integrable_cosetIndicator_mul hp H hHo hHc a η).const_mul (f a)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul]
    congr 1
    have := finFourier_cosetIndicator (ν := ν) hp H H' hHo hann a η
    unfold finFourier at this
    rw [this, mul_assoc]
  refine ⟨⟨?_, ?_⟩, fun x => ?_⟩
  · rw [hFf]
    refine isLocallyConstant_finset_sum s _ fun a _ => ?_
    exact (IsLocallyConstant.const (f a)).mul (((IsLocallyConstant.const _).mul
      (hp.isLocallyConstant_right a)).mul (isLocallyConstant_cosetIndicator H' hH'o 0))
  · refine HasCompactSupport.intro' hH'c (AddSubgroup.isClosed_of_isOpen H' hH'o)
      fun η hη => ?_
    have hη' : ¬ (η ∈ H') := hη
    rw [hFf]
    simp [cosetIndicator, hη']
  · have hterm : ∀ a η, f a * (ν.real H * p a η * cosetIndicator H' 0 η) * p η x =
        (f a * ν.real H) * (cosetIndicator H' 0 η * p η (a + x)) := by
      intro a η
      rw [hp.symm a η, hp.add_right]
      ring
    rw [hFf]
    unfold finFourier
    simp_rw [Finset.sum_mul, hterm]
    rw [integral_finsetSum _ fun a _ =>
      (integrable_cosetIndicator_mul hp H' hH'o hH'c 0 (a + x)).const_mul _]
    simp_rw [integral_const_mul]
    have hval : ∀ a, ∫ η, cosetIndicator H' 0 η * p η (a + x) ∂ν =
        ν.real H' * cosetIndicator H a (-x) := by
      intro a
      have hmem : -x - a ∈ H ↔ a + x ∈ H := by
        rw [show -x - a = -(a + x) by abel, neg_mem_iff]
      by_cases hax : a + x ∈ H
      · rw [integral_cosetIndicator_mul_of_forall hp H' hH'o 0 (a + x) ((hann' _).mpr hax),
          hp.zero_left]
        simp [cosetIndicator, hmem.mpr hax]
      · have : ¬ ∀ h ∈ H', p h (a + x) = 1 := fun h => hax ((hann' _).mp h)
        push Not at this
        obtain ⟨h₀, hh₀, hne⟩ := this
        rw [integral_cosetIndicator_mul_of_exists hp H' 0 (a + x) hh₀ hne]
        simp [cosetIndicator, mt hmem.mp hax]
    simp_rw [hval]
    rw [congrFun hs (-x), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end Generic

/-! ### The finite adeles -/

section FiniteAdeles

variable {F : Type u} [Field F] [NumberField F]

local instance finiteFourierMeasurableSpace : MeasurableSpace (FiniteAdeles F) := borel _

local instance finiteFourierBorelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩

local instance finiteFourierSecondCountable : SecondCountableTopology (FiniteAdeles F) :=
  finiteAdeles_secondCountableTopology F

local instance finiteFourierLocallyCompact : LocallyCompactSpace (FiniteAdeles F) :=
  finiteAdeles_locallyCompactSpace F

variable (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (n : ℕ)

/-- The pairing `(u, η) ↦ ψ_f(∑_j u_j η_j)` on `𝔸_f^n`. -/
def rowPairing (u η : Fin n → FiniteAdeles F) : ℂ := finiteCharacter F ψ (∑ j, u j * η j)

include hψ in
theorem isFinitePairing_rowPairing : IsFinitePairing (rowPairing ψ n) where
  add_left u u' η := by
    unfold rowPairing
    rw [← finiteCharacter_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, add_mul]
  symm u η := by
    unfold rowPairing
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  norm_eq u η := norm_finiteCharacter F ψ hψ _
  continuous_left η := (continuous_finiteCharacter ψ hψ).comp
    (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const)
  isLocallyConstant_right u := (isLocallyConstant_finiteCharacter ψ hψ).comp_continuous
    (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))

/-- **Finite-adelic Fourier inversion.** For an `L_m^n`-invariant compactly supported `f`
on `𝔸_f^n`, the transform for the additive Haar measure is locally constant with compact
support, and transforming twice gives `ν(L_m^n) ν(L_(n_ψ - m)^n) f(-x)`. -/
theorem finiteFourier_inversion (m : FinitePlace F →₀ ℤ) {f : (Fin n → FiniteAdeles F) → ℂ}
    (hf : HasCompactSupport f) (hinv : ∀ x, ∀ h ∈ latticeVec n m, f (x + h) = f x) :
    (IsLocallyConstant (finFourier Measure.addHaar (rowPairing ψ n) f) ∧
        HasCompactSupport (finFourier Measure.addHaar (rowPairing ψ n) f)) ∧
      ∀ x, finFourier Measure.addHaar (rowPairing ψ n)
          (finFourier Measure.addHaar (rowPairing ψ n) f) x =
        (Measure.addHaar : Measure (Fin n → FiniteAdeles F)).real (latticeVec n m) *
          (Measure.addHaar : Measure (Fin n → FiniteAdeles F)).real
            (latticeVec n (conductorDivisor ψ hψ - m)) * f (-x) := by
  refine finFourier_finFourier (isFinitePairing_rowPairing ψ hψ n) _ _
    (isOpen_latticeVec n m) (isCompact_latticeVec n m) (isOpen_latticeVec n _)
    (isCompact_latticeVec n _) (fun η => ?_) (fun x => ?_) hf hinv
  · exact forall_finiteCharacter_sum_eq_one_iff ψ hψ n m η
  · have := forall_finiteCharacter_sum_eq_one_iff ψ hψ n (conductorDivisor ψ hψ - m) x
    rwa [sub_sub_cancel] at this

end FiniteAdeles

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof
