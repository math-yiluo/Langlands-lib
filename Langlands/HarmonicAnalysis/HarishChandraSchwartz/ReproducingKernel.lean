import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

/-! # Reproducing kernels and finite dimensionality (Waldspurger VIII.4.1)

Waldspurger 2003, proof of Proposition VIII.4.1: the space `p_χ(°C_H)` carries the positive
definite hermitian product `(f₁, f₂) = ∫_{A_G \ G} conj (f₁ g) f₂(g) dg`, and has a
reproducing kernel `α_χ`: `(α_χ(·, g), f) = f(g)` (formula (1)). Since
`∫ α_χ(g, g) dg < ∞`, the space is finite dimensional and is spanned by the functions
`α_χ(·, g)`.

This module proves the functional-analytic step for an arbitrary measure space `X` and a
space `V` of square-integrable complex functions on `X` with a reproducing kernel `K`:
if `x ↦ Re K(x, x)` is integrable then `V` is finite dimensional, `dim V ≤ ∫ Re K(x, x)`,
`V` is spanned by the functions `K(·, x)`, and `K(y, x) = ∑ᵢ fᵢ(y) conj fᵢ(x)` for every
orthonormal basis `(fᵢ)` of `V`. The proof uses Bessel's inequality in `L²(X)`.
It also proves the first reduction of the proof: if `χ` is nontrivial on `A ∩ H` then
`p_χ` kills every `H`-bi-invariant function.
-/

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate InnerProductSpace

namespace Langlands.HarishChandraSchwartz

universe u v

section Kernel

variable {X : Type v} [MeasurableSpace X] {μ : Measure X}

/-- `K` is a reproducing kernel for the space `V` of complex functions on `X`, for the pairing
`(f₁, f₂) = ∫ conj f₁ · f₂ dμ`: every element of `V` is square integrable, every function
`K(·, x)` lies in `V`, and `(K(·, x), f) = ∫ f(y) conj K(y, x) dμ(y) = f(x)` for all `f ∈ V`
and `x ∈ X`. -/
structure IsReproducingKernel (μ : Measure X) (V : Submodule ℂ (X → ℂ)) (K : X → X → ℂ) :
    Prop where
  memLp : ∀ f ∈ V, MemLp f 2 μ
  mem : ∀ x, (fun y => K y x) ∈ V
  reproduce : ∀ f ∈ V, ∀ x, ∫ y, f y * conj (K y x) ∂μ = f x

namespace IsReproducingKernel

variable {V : Submodule ℂ (X → ℂ)} {K : X → X → ℂ}

/-- The function `K(·, x)` as an element of `V`. -/
def kernel (hK : IsReproducingKernel μ V K) (x : X) : V :=
  ⟨fun y => K y x, hK.mem x⟩

/-- The linear map `V → L²(μ)`. -/
def embed (hK : IsReproducingKernel μ V K) : V →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (hK.memLp f f.2).toLp f
  map_add' f g := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    rfl

variable (hK : IsReproducingKernel μ V K)
include hK

theorem coeFn_embed (f : V) : (hK.embed f : X → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (hK.memLp f f.2)

theorem inner_embed (f g : V) :
    ⟪hK.embed f, hK.embed g⟫_ℂ = ∫ y, conj ((f : X → ℂ) y) * (g : X → ℂ) y ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hK.coeFn_embed f, hK.coeFn_embed g] with y hf hg
  rw [hf, hg, RCLike.inner_apply']

/-- The reproducing property in `L²(μ)`: `⟪K(·, x), f⟫ = f(x)`. -/
theorem inner_embed_kernel (f : V) (x : X) :
    ⟪hK.embed (hK.kernel x), hK.embed f⟫_ℂ = (f : X → ℂ) x := by
  rw [hK.inner_embed, ← hK.reproduce f f.2 x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [kernel]
  ring

theorem embed_injective : Function.Injective hK.embed := by
  intro f g h
  apply Subtype.ext
  funext x
  rw [← hK.inner_embed_kernel f x, ← hK.inner_embed_kernel g x, h]

theorem norm_sq_embed (f : V) :
    ‖hK.embed f‖ ^ 2 = ∫ y, ‖(f : X → ℂ) y‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hK.inner_embed]
  have h : ∀ y, conj ((f : X → ℂ) y) * (f : X → ℂ) y = ((‖(f : X → ℂ) y‖ ^ 2 : ℝ) : ℂ) :=
    fun y => by rw [RCLike.conj_mul]; push_cast; rfl
  simp_rw [h, integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]

/-- `K(x, x) = ‖K(·, x)‖²`; in particular `K(x, x)` is real and nonnegative. -/
theorem kernel_diag (x : X) : K x x = ((‖hK.embed (hK.kernel x)‖ ^ 2 : ℝ) : ℂ) := by
  have h := hK.inner_embed_kernel (hK.kernel x) x
  rw [inner_self_eq_norm_sq_to_K] at h
  rw [show K x x = ((hK.kernel x : V) : X → ℂ) x from rfl, ← h]
  push_cast
  rfl

theorem kernel_diag_eq_integral (x : X) : K x x = ((∫ y, ‖K y x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [hK.kernel_diag, hK.norm_sq_embed]
  rfl

theorem re_kernel_diag (x : X) : (K x x).re = ‖hK.embed (hK.kernel x)‖ ^ 2 := by
  rw [hK.kernel_diag, Complex.ofReal_re]

theorem re_kernel_diag_nonneg (x : X) : 0 ≤ (K x x).re := by
  rw [hK.re_kernel_diag]
  positivity

/-- Bessel's inequality at a point: for `f₁, …, fₙ ∈ V` orthonormal in `L²(μ)`,
`∑ |fᵢ(x)|² ≤ K(x, x)`. -/
theorem sum_norm_sq_le {ι : Type*} (s : Finset ι) (v : ι → V)
    (hv : Orthonormal ℂ (hK.embed ∘ v)) (x : X) :
    ∑ i ∈ s, ‖(v i : X → ℂ) x‖ ^ 2 ≤ (K x x).re := by
  rw [hK.re_kernel_diag]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_)
    (hv.sum_inner_products_le (hK.embed (hK.kernel x)) (s := s))
  rw [Function.comp_apply, norm_inner_symm, hK.inner_embed_kernel]

/-- If `x ↦ Re K(x, x)` is integrable, every orthonormal family of `n` elements of `V` has
`n ≤ ∫ Re K(x, x) dμ`. -/
theorem card_le_of_orthonormal (hint : Integrable (fun x => (K x x).re) μ) {n : ℕ}
    (v : Fin n → V) (hv : Orthonormal ℂ (hK.embed ∘ v)) :
    (n : ℝ) ≤ ∫ x, (K x x).re ∂μ := by
  have hsq : ∀ i, Integrable (fun x => ‖(v i : X → ℂ) x‖ ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq_norm (hK.memLp _ (v i).2).aestronglyMeasurable).1 (hK.memLp _ (v i).2)
  have hn : (n : ℝ) = ∑ i, ∫ x, ‖(v i : X → ℂ) x‖ ^ 2 ∂μ := by
    have h1 : ∀ i, ‖hK.embed (v i)‖ = 1 := fun i => hv.1 i
    simp_rw [← hK.norm_sq_embed, h1]
    simp
  rw [hn, ← integral_finsetSum _ fun i _ => hsq i]
  exact integral_mono (integrable_finsetSum _ fun i _ => hsq i) hint
    (fun x => hK.sum_norm_sq_le Finset.univ v hv x)

theorem finrank_le_of_le_range (hint : Integrable (fun x => (K x x).re) μ)
    (E : Submodule ℂ (Lp ℂ 2 μ)) [FiniteDimensional ℂ E] (hE : E ≤ LinearMap.range hK.embed) :
    (finrank ℂ E : ℝ) ≤ ∫ x, (K x x).re ∂μ := by
  let b := stdOrthonormalBasis ℂ E
  have hmem : ∀ i, ((b i : E) : Lp ℂ 2 μ) ∈ LinearMap.range hK.embed := fun i => hE (b i).2
  choose v hv using hmem
  refine hK.card_le_of_orthonormal hint v ?_
  have h : hK.embed ∘ v = E.subtypeₗᵢ ∘ b := funext hv
  rw [h]
  exact b.orthonormal.comp_linearIsometry E.subtypeₗᵢ

/-- **Finite dimensionality** (Waldspurger, proof of Proposition VIII.4.1): a space of
square-integrable functions with a reproducing kernel `K` such that `x ↦ Re K(x, x)` is
integrable is finite dimensional. -/
theorem finiteDimensional (hint : Integrable (fun x => (K x x).re) μ) :
    FiniteDimensional ℂ V := by
  classical
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := ⌊∫ x, (K x x).re ∂μ⌋₊) fun s hs => ?_)
    Cardinal.natCast_lt_aleph0
  have hli := hs.map' hK.embed (LinearMap.ker_eq_bot.2 hK.embed_injective)
  let E := Submodule.span ℂ (Set.range (hK.embed ∘ fun i : s => (i : V)))
  have : FiniteDimensional ℂ E := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hE : E ≤ LinearMap.range hK.embed := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  have hcard : finrank ℂ E = s.card := by
    rw [finrank_span_eq_card hli]
    simp
  have h := hK.finrank_le_of_le_range hint E hE
  rw [hcard] at h
  exact Nat.le_floor h

/-- The dimension bound `dim V ≤ ∫ Re K(x, x) dμ`. -/
theorem finrank_le (hint : Integrable (fun x => (K x x).re) μ) :
    (finrank ℂ V : ℝ) ≤ ∫ x, (K x x).re ∂μ := by
  have := hK.finiteDimensional hint
  have h := hK.finrank_le_of_le_range hint (LinearMap.range hK.embed) le_rfl
  rwa [LinearMap.finrank_range_of_inj hK.embed_injective] at h

/-- **Spanning** (Waldspurger, end of the proof of Proposition VIII.4.1): under the
integrability hypothesis, `V` is spanned by the functions `K(·, x)`. -/
theorem span_kernel_eq_top (hint : Integrable (fun x => (K x x).re) μ) :
    Submodule.span ℂ (Set.range hK.kernel) = ⊤ := by
  have := hK.finiteDimensional hint
  set F := Submodule.span ℂ (Set.range hK.kernel)
  set P := F.map hK.embed
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨y, hy, z, hz, hyz⟩ := P.exists_add_mem_mem_orthogonal (hK.embed f)
  obtain ⟨g', hg'F, rfl⟩ := Submodule.mem_map.1 hy
  have hz' : z = hK.embed (f - g') := by rw [map_sub, hyz]; abel
  rw [hz'] at hz
  have h0 : ∀ x, ((f - g' : V) : X → ℂ) x = 0 := fun x => by
    rw [← hK.inner_embed_kernel (f - g') x]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem
      (Submodule.subset_span (⟨x, rfl⟩ : hK.kernel x ∈ Set.range hK.kernel))) hz
  have hg : f = g' := sub_eq_zero.1 (Subtype.ext (funext h0))
  rw [hg]
  exact hg'F

/-- Waldspurger's expansion `α_χ(g₁, g₂) = ∑ᵢ fᵢ(g₁) conj fᵢ(g₂)`: for every orthonormal
basis `(fᵢ)` of `V` (for the `L²(μ)` pairing), `K(y, x) = ∑ᵢ fᵢ(y) conj fᵢ(x)`. -/
theorem kernel_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (LinearMap.range hK.embed))
    (v : ι → V) (hv : ∀ i, hK.embed (v i) = b i) (x y : X) :
    K y x = ∑ i, (v i : X → ℂ) y * conj ((v i : X → ℂ) x) := by
  have hmem : ∀ z, hK.embed (hK.kernel z) ∈ LinearMap.range hK.embed := fun z => ⟨_, rfl⟩
  have h := b.sum_inner_mul_inner (⟨_, hmem y⟩ : LinearMap.range hK.embed) ⟨_, hmem x⟩
  have hk : ⟪(⟨_, hmem y⟩ : LinearMap.range hK.embed), ⟨_, hmem x⟩⟫_ℂ = K y x := by
    rw [Submodule.coe_inner, hK.inner_embed_kernel]
    rfl
  rw [← hk, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪(⟨_, hmem y⟩ : LinearMap.range hK.embed), b i⟫_ℂ = (v i : X → ℂ) y := by
    rw [Submodule.coe_inner, ← hv i, hK.inner_embed_kernel]
  have h2 : ⟪b i, (⟨_, hmem x⟩ : LinearMap.range hK.embed)⟫_ℂ = conj ((v i : X → ℂ) x) := by
    rw [← inner_conj_symm, Submodule.coe_inner, ← hv i, hK.inner_embed_kernel]
  rw [h1, h2]

end IsReproducingKernel

end Kernel

section Character

variable {G : Type u} [Group G] {A : Subgroup G} {χ : A →* ℂˣ}

/-- A `χ`-covariant function that is right invariant under `H` vanishes when `χ` is
nontrivial on `A ∩ H`, for central `A`. -/
theorem eq_zero_of_covariant (hA : A ≤ Subgroup.center G) {H : Subgroup G} {f : G → ℂ}
    (hcov : ∀ (a : A) (g : G), f ((a : G) * g) = χ a * f g)
    (hH : ∀ h ∈ H, ∀ g, f (g * h) = f g) {a : A} (ha : (a : G) ∈ H) (hχ : χ a ≠ 1) :
    f = 0 := by
  funext g
  have hc : g * (a : G) = (a : G) * g := Subgroup.mem_center_iff.mp (hA a.2) g
  have h1 : f g = χ a * f g := by rw [← hcov, ← hc, hH _ ha]
  have h2 : ((χ a : ℂ) - 1) * f g = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  have h3 : (χ a : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hχ (Units.ext h)
  simpa using (mul_eq_zero.1 h2).resolve_left h3

/-- The first reduction in the proof of Proposition VIII.4.1: if `χ` is nontrivial on
`A ∩ H` then `p_χ f = 0` for every `H`-bi-invariant `f`, so `p_χ(°C_H) = {0}`. -/
theorem centralProjection_eq_zero_of_ne_one [MeasurableSpace A] [MeasurableMul A]
    {μA : Measure A} [μA.IsMulRightInvariant]
    (hA : A ≤ Subgroup.center G) {H : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f)
    {a : A} (ha : (a : G) ∈ H) (hχ : χ a ≠ 1) :
    centralProjection μA χ f = 0 := by
  refine eq_zero_of_covariant hA (fun b g => centralProjection_mul_left f b g)
    (fun h hh g => ?_) ha hχ
  have := hf.centralProjection (μA := μA) hA χ 1 H.one_mem h hh g
  simpa using this

end Character

end Langlands.HarishChandraSchwartz
