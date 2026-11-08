import Langlands.Global.Hecke.AdelicLattice
import Langlands.Global.Hecke.LatticePoissonGeneral
import Langlands.Global.Hecke.ThetaDecay
import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionProof

/-!
# Poisson summation over a number field for tensor test functions

Let `K` be a number field with archimedean scales `aR, aC` (giving `T = addTrace aR aC` and the
pairing `B(x, y) = -T(x y)` on the mixed space `V`), finite local characters `ψ_v` satisfying the
additive product formula with finitely supported conductors `n`, and self-dual Haar measures
`μ_v`. For a finite set `S ⊇ supp n` and local functions `g_v`, `tensorCoeff S g` is the function
`γ ↦ ∏_{v ∈ S} g_v(γ)` on the elements of `K` integral outside `S` (and `0` elsewhere). This
module proves the Poisson summation formula

`∑_{γ ∈ K} a(γ) F(γ) = κ ∑_{w ∈ K} â(w) 𝓕F(w)`,   `κ = ∏ √|aR_v| ∏ 2 |aC_v|`,

for `a = tensorCoeff S g` with Schwartz–Bruhat `g_v`, `â = tensorCoeff S (𝓕_v g_v)` built from the
local Fourier transforms for `ψ_v, μ_v`, and `F` decaying polynomially together with its Fourier
transform `𝓕F w = ∫ 𝐞(T(x w)) F(x) dx` (`tsum_tensorCoeff_mul_eq`), and its theta-series form
`θ(a, F)(y) = N(y)⁻¹ θ(â, κ 𝓕F)(y⁻¹)` (`thetaSeries_tensorCoeff_eq`).

The proof expands each `g_v` into indicators of cosets of one valuation lattice. A tensor of
coset indicators is, by strong approximation, the indicator of a translate `γ₀ + I` of a
fractional ideal; lattice Poisson summation, the trace-dual `I^* = I'` and the Tamagawa
normalization of `Langlands.Global.Hecke.AdelicLattice` then give the coset case
(`tsum_tensorCoeff_cosetIndicator_mul_eq`).
-/

noncomputable section

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global.CompletionPadic
open scoped NumberField nonZeroDivisors
open Module NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real FourierTransform Classical

namespace Langlands.Global.Hecke

variable {K : Type*} [Field K] [NumberField K]

/-! ### Sums over ideal lattices -/

section IdealLattice

theorem mixedEmbedding_mem_idealLattice_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (γ : K) :
    mixedEmbedding K γ ∈ idealLattice K I ↔ γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_idealLattice]
  constructor
  · rintro ⟨γ', hγ', h⟩
    rwa [← mixedEmbedding_injective K h]
  · exact fun h => ⟨γ, h, rfl⟩

theorem indicator_idealLattice_mixedEmbedding (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : mixedSpace K → ℂ) (γ : K) :
    (idealLattice K I : Set (mixedSpace K)).indicator f (mixedEmbedding K γ) =
      ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator (fun γ => f (mixedEmbedding K γ)) γ := by
  by_cases hγ : γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)
  · rw [Set.indicator_of_mem ((mixedEmbedding_mem_idealLattice_iff I γ).mpr hγ),
      Set.indicator_of_mem (show γ ∈ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) from hγ)]
  · rw [Set.indicator_of_notMem (fun h => hγ ((mixedEmbedding_mem_idealLattice_iff I γ).mp h)),
      Set.indicator_of_notMem (show γ ∉ ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) from hγ)]

omit [NumberField K] in
theorem indicator_idealLattice_eq_zero_of_notMem_range (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : mixedSpace K → ℂ) (x : mixedSpace K) (hx : x ∉ Set.range (mixedEmbedding K)) :
    (idealLattice K I : Set (mixedSpace K)).indicator f x = 0 := by
  apply Set.indicator_of_notMem
  intro hmem
  obtain ⟨γ, -, rfl⟩ := (mem_idealLattice K I).mp hmem
  exact hx ⟨γ, rfl⟩

/-- A sum over the lattice of a fractional ideal is the corresponding sum over `K`. -/
theorem tsum_indicator_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : mixedSpace K → ℂ) :
    ∑' x : mixedSpace K, (idealLattice K I : Set (mixedSpace K)).indicator f x =
      ∑' γ : K, ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
        (fun γ => f (mixedEmbedding K γ)) γ := by
  have hsupp : Function.support ((idealLattice K I : Set (mixedSpace K)).indicator f) ⊆
      Set.range (mixedEmbedding K) := fun x hx => by
    by_contra hn
    exact hx (indicator_idealLattice_eq_zero_of_notMem_range I f x hn)
  rw [← (mixedEmbedding_injective K).tsum_eq hsupp]
  exact tsum_congr (indicator_idealLattice_mixedEmbedding I f)

theorem summable_indicator_idealLattice_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : mixedSpace K → ℂ) :
    Summable (fun γ : K => ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
        (fun γ => f (mixedEmbedding K γ)) γ) ↔
      Summable ((idealLattice K I : Set (mixedSpace K)).indicator f) := by
  have h : (fun γ : K => ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
      (fun γ => f (mixedEmbedding K γ)) γ) =
        (idealLattice K I : Set (mixedSpace K)).indicator f ∘ mixedEmbedding K :=
    funext fun γ => (indicator_idealLattice_mixedEmbedding I f γ).symm
  rw [h]
  exact (mixedEmbedding_injective K).summable_iff
    (indicator_idealLattice_eq_zero_of_notMem_range I f)

end IdealLattice

/-! ### Tensor coefficients on `K` -/

section Tensor

/-- `γ ∈ K` is integral at every finite place outside `S`. -/
def IntegralOutside (S : Finset (FinitePlace K)) (γ : K) : Prop :=
  ∀ v ∉ S, algebraMap K (FiniteCompletion K v) γ ∈ (topologicalData v).additiveLattice 0

/-- The global coefficient `γ ↦ ∏_{v ∈ S} g_v(γ) · ∏_{v ∉ S} 1_{O_v}(γ)` of a family of local
functions `g_v` on the completions. -/
def tensorCoeff (S : Finset (FinitePlace K)) (g : ∀ v : FinitePlace K, FiniteCompletion K v → ℂ)
    (γ : K) : ℂ :=
  if IntegralOutside S γ then ∏ v ∈ S, g v (algebraMap K (FiniteCompletion K v) γ) else 0

/-- The indicator of the coset `a + L_v(k)` of a valuation lattice. -/
def cosetIndicator (v : FinitePlace K) (a : FiniteCompletion K v) (k : ℤ)
    (x : FiniteCompletion K v) : ℂ :=
  {z : FiniteCompletion K v | z - a ∈ (topologicalData v).additiveLattice k}.indicator
    (fun _ => 1) x

/-- A tensor of coset indicators is the indicator of a translate `γ₀ + latticeIdeal m`. -/
theorem tensorCoeff_cosetIndicator_eq (S : Finset (FinitePlace K)) (m : FinitePlace K →₀ ℤ)
    (hmS : m.support ⊆ S) (a : ∀ v, FiniteCompletion K v) {γ₀ : K}
    (hγ₀S : ∀ v ∈ S, algebraMap K (FiniteCompletion K v) γ₀ - a v ∈
      (topologicalData v).additiveLattice (m v))
    (hγ₀out : ∀ v ∉ S, algebraMap K (FiniteCompletion K v) γ₀ ∈
      (topologicalData v).additiveLattice 0)
    (γ : K) :
    tensorCoeff S (fun v => cosetIndicator v (a v) (m v)) γ =
      ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator (fun _ => 1) (γ - γ₀) := by
  have hm0 : ∀ v ∉ S, m v = 0 := fun v hv =>
    Finsupp.notMem_support_iff.mp (fun h => hv (hmS h))
  by_cases h : γ - γ₀ ∈ (latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K)
  · rw [Set.indicator_of_mem (show γ - γ₀ ∈ ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) from h)]
    have hl := (mem_latticeIdeal_iff_forall_mem m _).mp h
    have hint : IntegralOutside S γ := fun v hv => by
      have h1 := hl v
      rw [hm0 v hv, map_sub] at h1
      have h2 := add_mem h1 (hγ₀out v hv)
      rwa [sub_add_cancel] at h2
    rw [tensorCoeff, ite_eq_left hint]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [cosetIndicator, Set.indicator_of_mem]
    show algebraMap K (FiniteCompletion K v) γ - a v ∈ (topologicalData v).additiveLattice (m v)
    have h1 := hl v
    rw [map_sub] at h1
    have h2 := add_mem h1 (hγ₀S v hv)
    rwa [sub_add_sub_cancel] at h2
  · rw [Set.indicator_of_notMem (show γ - γ₀ ∉ ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) from h)]
    have hl : ¬ ∀ v, algebraMap K (FiniteCompletion K v) (γ - γ₀) ∈
        (topologicalData v).additiveLattice (m v) :=
      fun h' => h ((mem_latticeIdeal_iff_forall_mem m _).mpr h')
    push Not at hl
    obtain ⟨v, hv⟩ := hl
    rw [tensorCoeff]
    split_ifs with hint
    · by_cases hvS : v ∈ S
      · refine Finset.prod_eq_zero hvS ?_
        rw [cosetIndicator, Set.indicator_of_notMem]
        intro hmem
        have hmem' : algebraMap K (FiniteCompletion K v) γ - a v ∈
            (topologicalData v).additiveLattice (m v) := hmem
        apply hv
        rw [map_sub]
        have h2 := sub_mem hmem' (hγ₀S v hvS)
        rwa [sub_sub_sub_cancel_right] at h2
      · exfalso
        apply hv
        rw [hm0 v hvS, map_sub]
        exact sub_mem (hint v hvS) (hγ₀out v hvS)
    · rfl

theorem tensorCoeff_congr (S : Finset (FinitePlace K))
    {g g' : ∀ v : FinitePlace K, FiniteCompletion K v → ℂ} (h : ∀ v ∈ S, g v = g' v) (γ : K) :
    tensorCoeff S g γ = tensorCoeff S g' γ := by
  unfold tensorCoeff
  rw [Finset.prod_congr rfl fun v hv => congrFun (h v hv) _]

/-- Expanding the local functions into finite sums expands the tensor coefficient into a sum
of tensor coefficients. -/
theorem tensorCoeff_eq_sum (S : Finset (FinitePlace K))
    (h : ∀ v : FinitePlace K, FiniteCompletion K v → ℂ) (N : FinitePlace K → ℕ)
    (c : ∀ v, Fin (N v) → ℂ) (k : ∀ v, Fin (N v) → FiniteCompletion K v → ℂ)
    (hh : ∀ v ∈ S, ∀ y, h v y = ∑ i, c v i * k v i y) (γ : K) :
    tensorCoeff S h γ = ∑ p : (∀ v : S, Fin (N v)), (∏ v : S, c v (p v)) *
      tensorCoeff S (fun v y => if hv : v ∈ S then k v (p ⟨v, hv⟩) y else 0) γ := by
  unfold tensorCoeff
  split_ifs with hint
  · rw [← Finset.prod_coe_sort S, Finset.prod_congr rfl (fun v _ => hh v.1 v.2 _),
      Fintype.prod_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.prod_coe_sort S, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [v.2, ↓reduceDIte]
  · simp

end Tensor

/-! ### Poisson summation for tensors of coset indicators -/

section CosetPoisson

variable {aR : {w : InfinitePlace K // IsReal w} → ℝ} {aC : {w : InfinitePlace K // IsComplex w} → ℂ}
  {ψf : ∀ v : FinitePlace K, @HarmonicAnalysis.UnitaryAdditiveCharacter
    (CompletionPadic.padicField v).Carrier _ (topologicalData v).topology}

/-- On the dual lattice, the product of the local characters at the coset centres is the
archimedean character of the global centre. -/
theorem prod_character_eq_fourierChar (hprod : AdditiveProductFormula aR aC ψf)
    (n : FinitePlace K →₀ ℤ) (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (S : Finset (FinitePlace K)) (hnS : n.support ⊆ S) (m : FinitePlace K →₀ ℤ)
    (hmS : m.support ⊆ S) (a : ∀ v, FiniteCompletion K v) {γ₀ : K}
    (hγ₀S : ∀ v ∈ S, algebraMap K (FiniteCompletion K v) γ₀ - a v ∈
      (topologicalData v).additiveLattice (m v))
    (hγ₀out : ∀ v ∉ S, algebraMap K (FiniteCompletion K v) γ₀ ∈
      (topologicalData v).additiveLattice 0)
    {w : K} (hw : w ∈ (latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K)) :
    ∏ v ∈ S, ((ψf v (a v * algebraMap K (FiniteCompletion K v) w) : Circle) : ℂ) =
      (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) (mixedEmbedding K w)) : ℂ) := by
  have hl := (mem_latticeIdeal_iff_forall_mem _ w).mp hw
  have hS1 : ∀ v ∈ S, ψf v (a v * algebraMap K (FiniteCompletion K v) w) =
      ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) := by
    intro v hv
    have h1 : (a v - algebraMap K (FiniteCompletion K v) γ₀) *
        algebraMap K (FiniteCompletion K v) w ∈
          (topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v)) := by
      have h0 := mul_mem_additiveLattice v (neg_mem (hγ₀S v hv)) (hl v)
      have h2 : m v + (n - m) v = (topologicalData v).additiveConductor (ψf v) := by
        rw [Finsupp.coe_sub, Pi.sub_apply, hn v]
        ring
      rwa [h2, neg_sub] at h0
    have h3 : a v * algebraMap K (FiniteCompletion K v) w =
        algebraMap K (FiniteCompletion K v) (γ₀ * w) +
          (a v - algebraMap K (FiniteCompletion K v) γ₀) *
            algebraMap K (FiniteCompletion K v) w := by
      rw [map_mul]
      ring
    rw [h3, AddChar.map_add_eq_mul (ψf v).toAddChar]
    change _ * ψf v _ = _
    rw [((topologicalData v).additiveConductor_spec (ψf v)).1 _ h1, mul_one]
  have hout : ∀ v ∉ S, ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) = 1 := by
    intro v hv
    apply ((topologicalData v).additiveConductor_spec (ψf v)).1
    have hn0 : (topologicalData v).additiveConductor (ψf v) = 0 := by
      rw [hn v]
      exact Finsupp.notMem_support_iff.mp (fun h => hv (hnS h))
    have hm0 : m v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hmS h))
    have hw0 : algebraMap K (FiniteCompletion K v) w ∈ (topologicalData v).additiveLattice 0 := by
      have h0 := hl v
      rwa [Finsupp.coe_sub, Pi.sub_apply, ← hn v, hn0, hm0, sub_zero] at h0
    rw [hn0, map_mul]
    simpa using mul_mem_additiveLattice v (hγ₀out v hv) hw0
  obtain ⟨S', hS'out, hS'⟩ := hprod (γ₀ * w)
  have hprodS : ∏ v ∈ S, ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) =
      ∏ v ∈ S', ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) := by
    rw [Finset.prod_subset Finset.subset_union_left (fun v _ hv => hout v hv),
      Finset.prod_subset (Finset.subset_union_right (s₁ := S)) (fun v _ hv => hS'out v hv)]
  have hC : ∏ v ∈ S, ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) =
      𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) (mixedEmbedding K w)) := by
    rw [hprodS, tracePairing_apply, ← map_mul, AddChar.map_neg_eq_inv]
    exact eq_inv_of_mul_eq_one_right hS'
  rw [← hC]
  have hcoe : ((∏ v ∈ S, ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) : Circle) : ℂ) =
      ∏ v ∈ S, ((ψf v (algebraMap K (FiniteCompletion K v) (γ₀ * w)) : Circle) : ℂ) :=
    map_prod Circle.coeHom _ _
  rw [hcoe]
  exact Finset.prod_congr rfl fun v hv => by rw [hS1 v hv]

variable (ψf) in
/-- The local Fourier transforms `y ↦ μ_v(L_v(m_v)) ψ_v(a_v y) 1_{L_v(n_v - m_v)}(y)` of the coset
indicators `1_{a_v + L_v(m_v)}`, `n_v` the additive conductor of `ψ_v`. -/
def dualCosetCoeff
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (m : FinitePlace K → ℤ) (a : ∀ v, FiniteCompletion K v) (v : FinitePlace K)
    (y : FiniteCompletion K v) : ℂ :=
  (latticeMass (topologicalData v) (ψf v) (μ v) (m v) : ℂ) * ((ψf v (a v * y) : Circle) : ℂ) *
    ((topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v) - m v) :
      Set (FiniteCompletion K v)).indicator (fun _ => 1) y

/-- The dual coefficients of a tensor of coset indicators: a constant times the indicator of the
dual ideal lattice, twisted by the archimedean character of the coset centre. -/
theorem tensorCoeff_dualCoset_eq (hprod : AdditiveProductFormula aR aC ψf)
    (n : FinitePlace K →₀ ℤ) (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (S : Finset (FinitePlace K)) (hnS : n.support ⊆ S) (m : FinitePlace K →₀ ℤ)
    (hmS : m.support ⊆ S) (a : ∀ v, FiniteCompletion K v) {γ₀ : K}
    (hγ₀S : ∀ v ∈ S, algebraMap K (FiniteCompletion K v) γ₀ - a v ∈
      (topologicalData v).additiveLattice (m v))
    (hγ₀out : ∀ v ∉ S, algebraMap K (FiniteCompletion K v) γ₀ ∈
      (topologicalData v).additiveLattice 0)
    (w : K) :
    tensorCoeff S (dualCosetCoeff ψf μ m a) w =
      (∏ v ∈ S, (latticeMass (topologicalData v) (ψf v) (μ v) (m v) : ℂ)) *
        ((latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
          (fun w => (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) (mixedEmbedding K w)) : ℂ)) w := by
  unfold dualCosetCoeff
  have hnm0 : ∀ v ∉ S, (n - m) v = 0 := fun v hv => by
    rw [Finsupp.coe_sub, Pi.sub_apply, Finsupp.notMem_support_iff.mp (fun h => hv (hnS h)),
      Finsupp.notMem_support_iff.mp (fun h => hv (hmS h)), sub_zero]
  have hnm : ∀ v, (n - m) v = (topologicalData v).additiveConductor (ψf v) - m v := fun v => by
    rw [Finsupp.coe_sub, Pi.sub_apply, hn v]
  by_cases h : w ∈ (latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K)
  · have hl := (mem_latticeIdeal_iff_forall_mem _ w).mp h
    have hint : IntegralOutside S w := fun v hv => by
      have h0 := hl v
      rwa [hnm0 v hv] at h0
    rw [tensorCoeff, ite_eq_left hint, Set.indicator_of_mem (show w ∈ ((latticeIdeal (n - m) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K) from h),
      ← prod_character_eq_fourierChar hprod n hn S hnS m hmS a hγ₀S hγ₀out h,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hv := hl v
    rw [hnm v] at hv
    rw [Set.indicator_of_mem (show algebraMap K (FiniteCompletion K v) w ∈
      ((topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v) - m v) :
        Set (FiniteCompletion K v)) from hv), mul_one]
  · rw [Set.indicator_of_notMem (show w ∉ ((latticeIdeal (n - m) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K) from h), mul_zero]
    have hl : ¬ ∀ v, algebraMap K (FiniteCompletion K v) w ∈
        (topologicalData v).additiveLattice ((n - m) v) :=
      fun h' => h ((mem_latticeIdeal_iff_forall_mem _ w).mpr h')
    push Not at hl
    obtain ⟨v, hv⟩ := hl
    rw [tensorCoeff]
    split_ifs with hint
    · by_cases hvS : v ∈ S
      · refine Finset.prod_eq_zero hvS ?_
        rw [hnm v] at hv
        rw [Set.indicator_of_notMem (show algebraMap K (FiniteCompletion K v) w ∉
          ((topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v) -
            m v) : Set (FiniteCompletion K v)) from hv), mul_zero]
      · exfalso
        apply hv
        rw [hnm0 v hvS]
        exact hint v hvS
    · rfl

/-- **Poisson summation over `K` for a tensor of coset indicators.** Let the archimedean scales
be nonzero, the local characters satisfy the additive product formula with conductors `n`, `μ_v`
be self-dual, and `S ⊇ supp n ∪ supp m`. For `F` on the mixed space decaying with its Fourier
transform `𝓕 F w = ∫ 𝐞(T(x w)) F(x) dx` like `(1 + ‖x‖)^{-r}`, `r > [K : ℚ]`,
`∑_{γ ∈ K} ∏_v 1_{a_v + L_v(m_v)}(γ) F(γ) = κ ∑_{w ∈ K} ∏_v 𝓕_v(1_{a_v + L_v(m_v)})(w) 𝓕F(w)`,
where outside `S` the factors are `1_{O_v}` and `𝓕_v(1_{a + L(k)})(y) = μ_v(L(k)) ψ_v(a y)
1_{L(n_v - k)}(y)`. -/
theorem tsum_tensorCoeff_cosetIndicator_mul_eq (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (hprod : AdditiveProductFormula aR aC ψf)
    (n : FinitePlace K →₀ ℤ) (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (S : Finset (FinitePlace K)) (hnS : n.support ⊆ S) (m : FinitePlace K →₀ ℤ)
    (hmS : m.support ⊆ S) (a : ∀ v, FiniteCompletion K v)
    (F : C(mixedSpace K, ℂ)) {C C' r : ℝ} (hr : (finrank ℝ (mixedSpace K) : ℝ) < r)
    (hF : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-r))
    (hFF : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w‖ ≤
      C' * (1 + ‖w‖) ^ (-r)) :
    ∑' γ : K, tensorCoeff S (fun v => cosetIndicator v (a v) (m v)) γ *
        F (mixedEmbedding K γ) =
      mixedGaussianConst aR aC * ∑' w : K,
        tensorCoeff S (dualCosetCoeff ψf μ m a) w *
          VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F (mixedEmbedding K w) := by
  -- the global centre of the coset
  obtain ⟨γ₀, hγ₀S, hγ₀out⟩ := exists_approx S a (fun v => m v)
  have hB := tracePairing_nondegenerate haR haC
  -- the left side is a lattice sum
  have hL : ∑' γ : K, tensorCoeff S (fun v => cosetIndicator v (a v) (m v)) γ *
      F (mixedEmbedding K γ) =
        ∑' l : idealLattice K (latticeIdeal m), F (mixedEmbedding K γ₀ + l) := by
    calc ∑' γ : K, tensorCoeff S (fun v => cosetIndicator v (a v) (m v)) γ *
          F (mixedEmbedding K γ) =
        ∑' γ : K, ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
          (fun t => F (mixedEmbedding K γ₀ + mixedEmbedding K t)) (γ - γ₀) := by
          refine tsum_congr fun γ => ?_
          rw [tensorCoeff_cosetIndicator_eq S m hmS a hγ₀S hγ₀out]
          by_cases h : γ - γ₀ ∈ ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) : Set K)
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul, map_sub,
              add_sub_cancel]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
      _ = ∑' t : K, ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
          (fun t => F (mixedEmbedding K γ₀ + mixedEmbedding K t)) t :=
        (Equiv.subRight γ₀).tsum_eq _
      _ = ∑' x : mixedSpace K, (idealLattice K (latticeIdeal m) : Set (mixedSpace K)).indicator
          (fun y => F (mixedEmbedding K γ₀ + y)) x :=
        (tsum_indicator_idealLattice (latticeIdeal m) (fun y => F (mixedEmbedding K γ₀ + y))).symm
      _ = ∑' l : idealLattice K (latticeIdeal m), F (mixedEmbedding K γ₀ + l) :=
        (tsum_subtype (idealLattice K (latticeIdeal m) : Set (mixedSpace K)) _).symm
  -- Poisson summation for the ideal lattice
  have hsum := summable_dualSubmodule_of_decay hB (idealLattice K (latticeIdeal m)) hr hFF
  have hP := tsum_add_zlattice_eq hB (idealLattice K (latticeIdeal m)) volume F hr hF hsum
    (mixedEmbedding K γ₀)
  -- the dual lattice sum as a sum over `K`
  have hD : ∑' w : (tracePairing aR aC).flip.dualSubmodule (idealLattice K (latticeIdeal m)),
      VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w *
        (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) w) : ℂ) =
      ∑' w : K, ((latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
        (fun w => VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F
          (mixedEmbedding K w) *
          (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) (mixedEmbedding K w)) : ℂ)) w := by
    calc _ = ∑' x : mixedSpace K, (((tracePairing aR aC).flip.dualSubmodule
          (idealLattice K (latticeIdeal m)) : Submodule ℤ (mixedSpace K)) :
            Set (mixedSpace K)).indicator
          (fun w => VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w *
            (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) w) : ℂ)) x :=
          tsum_subtype _ _
      _ = ∑' x : mixedSpace K, (idealLattice K (latticeIdeal (n - m)) :
            Set (mixedSpace K)).indicator
          (fun w => VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w *
            (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) w) : ℂ)) x := by
          rw [dualSubmodule_idealLattice haR haC hprod n hn m]
      _ = _ := tsum_indicator_idealLattice _ _
  -- the right side
  have hR : ∑' w : K,
      tensorCoeff S (dualCosetCoeff ψf μ m a) w *
        VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F (mixedEmbedding K w) =
      (∏ v ∈ S, (latticeMass (topologicalData v) (ψf v) (μ v) (m v) : ℂ)) *
        ∑' w : K, ((latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K) : Set K).indicator
          (fun w => VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F
            (mixedEmbedding K w) *
            (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) (mixedEmbedding K w)) : ℂ)) w := by
    rw [← tsum_mul_left]
    refine tsum_congr fun w => ?_
    rw [tensorCoeff_dualCoset_eq hprod n hn μ S hnS m hmS a hγ₀S hγ₀out]
    by_cases h : w ∈ ((latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K) : Set K)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  -- the Tamagawa normalization
  have hT := mixedGaussianConst_mul_covolume_mul_prod_latticeMass haR haC hprod n hn μ m S hmS hnS
  have hTc : (mixedGaussianConst aR aC : ℂ) *
      (ZLattice.covolume (idealLattice K (latticeIdeal m)) : ℂ) *
        ∏ v ∈ S, (latticeMass (topologicalData v) (ψf v) (μ v) (m v) : ℂ) = 1 := by
    exact_mod_cast hT
  have hinv : (mixedGaussianConst aR aC : ℂ) *
      ∏ v ∈ S, (latticeMass (topologicalData v) (ψf v) (μ v) (m v) : ℂ) =
        (((ZLattice.covolume (idealLattice K (latticeIdeal m)))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
    exact eq_inv_of_mul_eq_one_right (by linear_combination hTc)
  rw [hL, hP, hD, hR, ← hinv]
  ring

/-- The left side of the coset-tensor Poisson formula is absolutely summable over `K`. -/
theorem summable_tensorCoeff_cosetIndicator_mul (S : Finset (FinitePlace K))
    (m : FinitePlace K →₀ ℤ) (hmS : m.support ⊆ S) (a : ∀ v, FiniteCompletion K v)
    (F : C(mixedSpace K, ℂ)) {C r : ℝ} (hr : (finrank ℝ (mixedSpace K) : ℝ) < r)
    (hF : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-r)) :
    Summable fun γ : K => tensorCoeff S (fun v => cosetIndicator v (a v) (m v)) γ *
      F (mixedEmbedding K γ) := by
  obtain ⟨γ₀, hγ₀S, hγ₀out⟩ := exists_approx S a (fun v => m v)
  have h1 := summable_add_zlattice_of_decay (idealLattice K (latticeIdeal m)) hr hF
    (mixedEmbedding K γ₀)
  have h2 := (summable_subtype_iff_indicator (s := (idealLattice K (latticeIdeal m) :
    Set (mixedSpace K))) (f := fun y => F (mixedEmbedding K γ₀ + y))).mp h1
  rw [← summable_indicator_idealLattice_iff] at h2
  have h3 := (Equiv.subRight γ₀).summable_iff.mpr h2
  refine h3.congr fun γ => ?_
  simp only [Function.comp_apply, Equiv.subRight_apply]
  rw [tensorCoeff_cosetIndicator_eq S m hmS a hγ₀S hγ₀out]
  by_cases h : γ - γ₀ ∈ ((latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) : Set K)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul, map_sub, add_sub_cancel]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- The right side of the coset-tensor Poisson formula is absolutely summable over `K`. -/
theorem summable_tensorCoeff_dualCoset_mul (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (hprod : AdditiveProductFormula aR aC ψf)
    (n : FinitePlace K →₀ ℤ) (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (S : Finset (FinitePlace K)) (hnS : n.support ⊆ S) (m : FinitePlace K →₀ ℤ)
    (hmS : m.support ⊆ S) (a : ∀ v, FiniteCompletion K v)
    (F : C(mixedSpace K, ℂ)) {C' r : ℝ} (hr : (finrank ℝ (mixedSpace K) : ℝ) < r)
    (hFF : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w‖ ≤
      C' * (1 + ‖w‖) ^ (-r)) :
    Summable fun w : K =>
      tensorCoeff S (dualCosetCoeff ψf μ m a) w *
        VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F (mixedEmbedding K w) := by
  obtain ⟨γ₀, hγ₀S, hγ₀out⟩ := exists_approx S a (fun v => m v)
  have hB := tracePairing_nondegenerate haR haC
  have hG : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w *
      (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) w) : ℂ)‖ ≤ C' * (1 + ‖w‖) ^ (-r) :=
    fun w => by rw [norm_mul, Circle.norm_coe, mul_one]; exact hFF w
  have h1 := summable_dualSubmodule_of_decay hB (idealLattice K (latticeIdeal m)) hr hG
  have h2 := (summable_subtype_iff_indicator (s := (((tracePairing aR aC).flip.dualSubmodule
    (idealLattice K (latticeIdeal m)) : Submodule ℤ (mixedSpace K)) : Set (mixedSpace K)))
    (f := fun w => VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w *
      (𝐞 (tracePairing aR aC (mixedEmbedding K γ₀) w) : ℂ))).mp h1
  rw [dualSubmodule_idealLattice haR haC hprod n hn m,
    ← summable_indicator_idealLattice_iff] at h2
  refine (h2.mul_left (∏ v ∈ S, (latticeMass (topologicalData v) (ψf v) (μ v) (m v) : ℂ))).congr
    fun w => ?_
  rw [tensorCoeff_dualCoset_eq hprod n hn μ S hnS m hmS a hγ₀S hγ₀out]
  by_cases h : w ∈ ((latticeIdeal (n - m) : FractionalIdeal (𝓞 K)⁰ K) : Set K)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    ring

end CosetPoisson

/-! ### Poisson summation for tensors of Schwartz–Bruhat functions -/

section TensorPoisson

variable {aR : {w : InfinitePlace K // IsReal w} → ℝ} {aC : {w : InfinitePlace K // IsComplex w} → ℂ}
  {ψf : ∀ v : FinitePlace K, @HarmonicAnalysis.UnitaryAdditiveCharacter
    (CompletionPadic.padicField v).Carrier _ (topologicalData v).topology}

variable (ψf) in
/-- The local Fourier transform `𝓕_v g (y) = ∫ ψ_v(x y) g(x) dμ_v(x)` of a Schwartz–Bruhat
function on `K_v`, for the self-dual Haar measure `μ_v`. -/
def localFourier
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (v : FinitePlace K)
    (g : @HarmonicAnalysis.SchwartzBruhat (CompletionPadic.padicField v).Carrier
      (topologicalData v).topology)
    (y : FiniteCompletion K v) : ℂ :=
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  HarmonicAnalysis.fourierTransform (ψf v) (μ v).val g y

/-- The local Fourier transform of a finite combination of coset indicators. -/
theorem localFourier_eq_sum
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (v : FinitePlace K)
    (g : @HarmonicAnalysis.SchwartzBruhat (CompletionPadic.padicField v).Carrier
      (topologicalData v).topology)
    {N : ℕ} (c : Fin N → ℂ) (a : Fin N → FiniteCompletion K v) (m : ℤ)
    (hg : ∀ x, g x = ∑ i, c i * cosetIndicator v (a i) m x) (y : FiniteCompletion K v) :
    localFourier ψf μ v g y = ∑ i, c i *
      ((latticeMass (topologicalData v) (ψf v) (μ v) m : ℂ) * ((ψf v (a i * y) : Circle) : ℂ) *
        ((topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v) - m) :
          Set (FiniteCompletion K v)).indicator (fun _ => 1) y) := by
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  have : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  have hF := HarmonicAnalysis.padicLatticeFourier (CompletionPadic.padicField v)
    (topologicalData v) (ψf v) (μ v).val m
  change ∫ x, (ψf v).complex (x * y) * g x ∂(μ v).val.measure = _
  simp_rw [hg, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨-, h⟩ := hF (a i) y
    simp_rw [mul_left_comm _ (c i)]
    rw [integral_const_mul]
    congr 1
  · intro i _
    obtain ⟨h, -⟩ := hF (a i) y
    simp_rw [mul_left_comm _ (c i)]
    exact h.const_mul _

/-- **Poisson summation over `K` for tensors of Schwartz–Bruhat functions.** Let the archimedean
scales be nonzero, the local characters `ψ_v` satisfy the additive product formula with
conductors forming the finitely supported `n`, `μ_v` be self-dual Haar measures and
`S ⊇ supp n`. For Schwartz–Bruhat functions `g_v` and a continuous `F` on the mixed space which
decays, together with `𝓕F w = ∫ 𝐞(T(x w)) F(x) dx`, like `(1 + ‖x‖)^{-r}` with `r > [K : ℚ]`,
`∑_{γ ∈ K} a(γ) F(γ) = κ ∑_{w ∈ K} â(w) 𝓕F(w)`, where `a(γ) = ∏_{v ∈ S} g_v(γ)` if `γ` is
integral outside `S` (and `0` otherwise) and `â` is built in the same way from the local
Fourier transforms `𝓕_v g_v`. -/
theorem tsum_tensorCoeff_mul_eq (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (hprod : AdditiveProductFormula aR aC ψf)
    (n : FinitePlace K →₀ ℤ) (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (S : Finset (FinitePlace K)) (hnS : n.support ⊆ S)
    (g : ∀ v : FinitePlace K, @HarmonicAnalysis.SchwartzBruhat
      (CompletionPadic.padicField v).Carrier (topologicalData v).topology)
    (F : C(mixedSpace K, ℂ)) {C C' r : ℝ} (hr : (finrank ℝ (mixedSpace K) : ℝ) < r)
    (hF : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-r))
    (hFF : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w‖ ≤
      C' * (1 + ‖w‖) ^ (-r)) :
    ∑' γ : K, tensorCoeff S (fun v y => g v y) γ * F (mixedEmbedding K γ) =
      mixedGaussianConst aR aC * ∑' w : K, tensorCoeff S (fun v => localFourier ψf μ v (g v)) w *
        VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F (mixedEmbedding K w) := by
  -- expand every local function into coset indicators of one lattice
  have hexp : ∀ v : FinitePlace K, ∃ (mv : ℤ) (Nv : ℕ) (cv : Fin Nv → ℂ)
      (av : Fin Nv → FiniteCompletion K v), ∀ x, g v x = ∑ i, cv i * cosetIndicator v (av i) mv x :=
    fun v => HarmonicAnalysis.padicLatticeSchwartzExpansion (CompletionPadic.padicField v)
      (topologicalData v) (g v)
  choose mE NE cE aE hE using hexp
  let m : FinitePlace K →₀ ℤ := Finsupp.onFinset S (fun v => if v ∈ S then mE v else 0)
    (fun v hv => by
      by_contra h
      exact hv (by simp [h]))
  have hmS : m.support ⊆ S := Finsupp.support_onFinset_subset
  have hmv : ∀ v ∈ S, m v = mE v := fun v hv => by simp [m, hv]
  let ap : (∀ v : S, Fin (NE v)) → ∀ v, FiniteCompletion K v := fun p v =>
    if hv : v ∈ S then aE v (p ⟨v, hv⟩) else 0
  let Cp : (∀ v : S, Fin (NE v)) → ℂ := fun p => ∏ v : S, cE v (p v)
  set 𝓕F := VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) (F : mixedSpace K → ℂ)
    with h𝓕F
  -- the expanded coefficients
  have hL : ∀ γ, tensorCoeff S (fun v y => g v y) γ =
      ∑ p, Cp p * tensorCoeff S (fun v => cosetIndicator v (ap p v) (m v)) γ := by
    intro γ
    rw [tensorCoeff_eq_sum S _ NE cE (fun v i => cosetIndicator v (aE v i) (mE v))
      (fun v _ y => hE v y)]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    refine tensorCoeff_congr S (fun v hv => funext fun y => ?_) γ
    simp only [hv, ↓reduceDIte, ap, hmv v hv]
  have hR : ∀ w, tensorCoeff S (fun v => localFourier ψf μ v (g v)) w =
      ∑ p, Cp p * tensorCoeff S (dualCosetCoeff ψf μ m (ap p)) w := by
    intro w
    rw [tensorCoeff_eq_sum S _ NE cE (fun v i y =>
        (latticeMass (topologicalData v) (ψf v) (μ v) (mE v) : ℂ) *
          ((ψf v (aE v i * y) : Circle) : ℂ) *
            ((topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v) -
              mE v) : Set (FiniteCompletion K v)).indicator (fun _ => 1) y)
      (fun v _ y => localFourier_eq_sum μ v (g v) (cE v) (aE v) (mE v) (hE v) y)]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    refine tensorCoeff_congr S (fun v hv => funext fun y => ?_) w
    simp only [hv, ↓reduceDIte, ap, hmv v hv, dualCosetCoeff]
  -- summability of the pieces
  have hsL : ∀ p ∈ (Finset.univ : Finset (∀ v : S, Fin (NE v))), Summable fun γ : K =>
      Cp p * (tensorCoeff S (fun v => cosetIndicator v (ap p v) (m v)) γ *
        F (mixedEmbedding K γ)) :=
    fun p _ => (summable_tensorCoeff_cosetIndicator_mul S m hmS (ap p) F hr hF).mul_left _
  have hsR : ∀ p ∈ (Finset.univ : Finset (∀ v : S, Fin (NE v))), Summable fun w : K =>
      Cp p * (tensorCoeff S (dualCosetCoeff ψf μ m (ap p)) w * 𝓕F (mixedEmbedding K w)) :=
    fun p _ => (summable_tensorCoeff_dualCoset_mul haR haC hprod n hn μ S hnS m hmS (ap p) F hr
      hFF).mul_left _
  calc ∑' γ : K, tensorCoeff S (fun v y => g v y) γ * F (mixedEmbedding K γ)
      = ∑' γ : K, ∑ p, Cp p * (tensorCoeff S (fun v => cosetIndicator v (ap p v) (m v)) γ *
          F (mixedEmbedding K γ)) := by
        refine tsum_congr fun γ => ?_
        rw [hL, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => mul_assoc _ _ _
    _ = ∑ p, Cp p * ∑' γ : K, tensorCoeff S (fun v => cosetIndicator v (ap p v) (m v)) γ *
          F (mixedEmbedding K γ) := by
        rw [Summable.tsum_finsetSum hsL]
        exact Finset.sum_congr rfl fun p _ => tsum_mul_left
    _ = ∑ p, Cp p * (mixedGaussianConst aR aC * ∑' w : K,
          tensorCoeff S (dualCosetCoeff ψf μ m (ap p)) w * 𝓕F (mixedEmbedding K w)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [tsum_tensorCoeff_cosetIndicator_mul_eq haR haC hprod n hn μ S hnS m hmS (ap p) F hr hF
          hFF]
    _ = mixedGaussianConst aR aC * ∑' w : K, ∑ p, Cp p *
          (tensorCoeff S (dualCosetCoeff ψf μ m (ap p)) w * 𝓕F (mixedEmbedding K w)) := by
        rw [Summable.tsum_finsetSum hsR, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [tsum_mul_left]
        ring
    _ = _ := by
        congr 1
        refine tsum_congr fun w => ?_
        rw [hR, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => (mul_assoc _ _ _).symm

end TensorPoisson

/-! ### Theta series -/

section Theta

/-- A point of nonzero norm has all coordinates bounded below by a positive constant. -/
theorem exists_pos_le_normAtPlace {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ w, m ≤ normAtPlace w y := by
  have hpos : ∀ w, 0 < normAtPlace w y := fun w => by
    refine lt_of_le_of_ne (normAtPlace_nonneg w y) (fun h => hy ?_)
    exact mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h.symm⟩
  exact ⟨Finset.univ.inf' Finset.univ_nonempty (fun w => normAtPlace w y),
    (Finset.lt_inf'_iff _).mpr fun w _ => hpos w, fun w => Finset.inf'_le _ (Finset.mem_univ w)⟩

/-- Polynomial decay is preserved by multiplication with a point of nonzero norm. -/
theorem exists_decay_comp_mul {G : mixedSpace K → ℂ} {C r : ℝ} (hr : 0 ≤ r)
    (hG : ∀ x, ‖G x‖ ≤ C * (1 + ‖x‖) ^ (-r)) {y : mixedSpace K}
    (hy : mixedEmbedding.norm y ≠ 0) :
    ∃ C₁ : ℝ, ∀ z, ‖G (y * z)‖ ≤ C₁ * (1 + ‖z‖) ^ (-r) := by
  obtain ⟨m, hm, hmy⟩ := exists_pos_le_normAtPlace hy
  have hC : 0 ≤ C := nonneg_of_decay hG
  refine ⟨C * (1 + m⁻¹) ^ r, fun z => (hG _).trans ?_⟩
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine rpow_neg_le_of_le_mul (by positivity) (by positivity) hr ?_
  have h1 := mul_norm_le_norm_mul hmy z
  rw [mul_comm z y] at h1
  have h2 : ‖z‖ ≤ m⁻¹ * ‖y * z‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ hm]
    linarith
  have h3 : (1 + m⁻¹) * (1 + ‖y * z‖) = 1 + ‖y * z‖ + m⁻¹ + m⁻¹ * ‖y * z‖ := by ring
  rw [h3]
  have := norm_nonneg (y * z)
  have := inv_pos.mpr hm
  linarith

variable {aR : {w : InfinitePlace K // IsReal w} → ℝ} {aC : {w : InfinitePlace K // IsComplex w} → ℂ}
  {ψf : ∀ v : FinitePlace K, @HarmonicAnalysis.UnitaryAdditiveCharacter
    (CompletionPadic.padicField v).Carrier _ (topologicalData v).topology}

/-- **Poisson summation for theta series of tensor coefficients.** Under the hypotheses of
`tsum_tensorCoeff_mul_eq`, for every `y` of nonzero norm,
`θ(a, F)(y) = N(y)⁻¹ θ(â, κ 𝓕F)(y⁻¹)`, where `θ(a, F)(y) = ∑_{γ ∈ K} a(γ) F(γ y)`. -/
theorem thetaSeries_tensorCoeff_eq (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (hprod : AdditiveProductFormula aR aC ψf)
    (n : FinitePlace K →₀ ℤ) (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (S : Finset (FinitePlace K)) (hnS : n.support ⊆ S)
    (g : ∀ v : FinitePlace K, @HarmonicAnalysis.SchwartzBruhat
      (CompletionPadic.padicField v).Carrier (topologicalData v).topology)
    (F : C(mixedSpace K, ℂ)) {C C' r : ℝ} (hr : (finrank ℝ (mixedSpace K) : ℝ) < r)
    (hF : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ (-r))
    (hFF : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w‖ ≤
      C' * (1 + ‖w‖) ^ (-r))
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    thetaSeries (tensorCoeff S (fun v x => g v x)) F y =
      (mixedEmbedding.norm y : ℂ)⁻¹ *
        thetaSeries (tensorCoeff S (fun v => localFourier ψf μ v (g v)))
          (fun w => (mixedGaussianConst aR aC : ℂ) *
            VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F w) y⁻¹ := by
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr.le
  let Fy : C(mixedSpace K, ℂ) :=
    ⟨fun z => F (y * z), F.continuous.comp (continuous_const.mul continuous_id)⟩
  obtain ⟨C₁, hC₁⟩ := exists_decay_comp_mul hr0 hF hy
  have hFy : ∀ w, VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) Fy w =
      ((mixedEmbedding.norm y)⁻¹ : ℝ) *
        VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) F (y⁻¹ * w) :=
    fun w => fourierIntegral_comp_mul aR aC F hy w
  have hy' : mixedEmbedding.norm y⁻¹ ≠ 0 := by
    intro h0
    have h1 : mixedEmbedding.norm (y * y⁻¹) = 1 := by
      rw [mul_inv_cancel_of_norm_ne_zero hy, map_one]
    rw [map_mul, h0, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨C₂, hC₂⟩ := exists_decay_comp_mul hr0 hFF hy'
  have hFFy : ∀ w, ‖VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) Fy w‖ ≤
      (|(mixedEmbedding.norm y)⁻¹| * C₂) * (1 + ‖w‖) ^ (-r) := fun w => by
    rw [hFy, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC₂ w) (abs_nonneg _)
  have h := tsum_tensorCoeff_mul_eq haR haC hprod n hn μ S hnS g Fy hr hC₁ hFFy
  unfold thetaSeries
  calc ∑' γ : K, tensorCoeff S (fun v x => g v x) γ * F (mixedEmbedding K γ * y)
      = ∑' γ : K, tensorCoeff S (fun v x => g v x) γ * Fy (mixedEmbedding K γ) := by
        refine tsum_congr fun γ => ?_
        change _ = _ * F (y * mixedEmbedding K γ)
        rw [mul_comm y]
    _ = _ := h
    _ = _ := by
        rw [← tsum_mul_left, ← tsum_mul_left]
        refine tsum_congr fun w => ?_
        rw [hFy, mul_comm y⁻¹ (mixedEmbedding K w)]
        push_cast
        ring

end Theta

end Langlands.Global.Hecke
