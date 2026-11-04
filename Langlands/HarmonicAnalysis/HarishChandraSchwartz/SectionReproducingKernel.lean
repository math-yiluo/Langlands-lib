import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Reproducing kernels read through a section (Waldspurger VIII.4.1)

In the proof of Proposition VIII.4.1, the space `p_χ(°C_H)` consists of functions on `G` that
are `χ`-covariant under `A_G`. The hermitian product on it is an integral over `A_G \ G` of
`conj(f₁) f₂`, which descends to the quotient although `f₁` and `f₂` do not.

This module proves the finite-dimensionality step for such spaces. Let `V` be a space of
complex functions on a type `Y`, `s : X → Y` any map from a measure space `X` (in the
application a section of `G → A_G \ G`), and assume that the products
`x ↦ f(s x) conj(g(s x))` are integrable for `f, g ∈ V`. If `K : Y → V` reproduces every
`f ∈ V`, i.e. `∫ f(s x) conj(K(y)(s x)) dμ(x) = f(y)` for all `y`, and the diagonal
`x ↦ Re K(s x)(s x)` is integrable, then `V` is finite dimensional, of dimension at most the
integral of the diagonal, and is spanned by the functions `K(y)`. No measurability of `f ∘ s`
itself is required.
-/

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate InnerProductSpace

namespace Langlands.HarishChandraSchwartz

universe u v

variable {X : Type u} [MeasurableSpace X] {Y : Type v}

/-- `K` is a reproducing kernel for the space `V` of functions on `Y`, read through `s`: the
products `f(s x) conj(g(s x))` are integrable for `f, g ∈ V`, and
`∫ f(s x) conj(K(y)(s x)) dμ(x) = f(y)` for all `f ∈ V` and `y ∈ Y`. -/
structure IsSectionReproducingKernel (μ : Measure X) (s : X → Y) (V : Submodule ℂ (Y → ℂ))
    (K : Y → V) : Prop where
  integrable : ∀ f ∈ V, ∀ g ∈ V, Integrable (fun x => f (s x) * conj (g (s x))) μ
  reproduce : ∀ f ∈ V, ∀ y, ∫ x, f (s x) * conj ((K y : Y → ℂ) (s x)) ∂μ = f y

/-- The form `B(f, g) = ∫ f(s x) conj(g(s x)) dμ(x)`. -/
def sectionForm (μ : Measure X) (s : X → Y) (f g : Y → ℂ) : ℂ :=
  ∫ x, f (s x) * conj (g (s x)) ∂μ

theorem sectionForm_swap (μ : Measure X) (s : X → Y) (f g : Y → ℂ) :
    sectionForm μ s g f = conj (sectionForm μ s f g) := by
  unfold sectionForm
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, Complex.conj_conj, mul_comm]

namespace IsSectionReproducingKernel

variable {μ : Measure X} {s : X → Y} {V : Submodule ℂ (Y → ℂ)} {K : Y → V}
  (hK : IsSectionReproducingKernel μ s V K)

section Form

include hK

theorem sectionForm_add_left (f f' g : V) :
    sectionForm μ s ((f + f' : V) : Y → ℂ) g = sectionForm μ s f g + sectionForm μ s f' g := by
  unfold sectionForm
  rw [← integral_add (hK.integrable f f.2 g g.2) (hK.integrable f' f'.2 g g.2)]
  congr 1
  funext x
  simp only [Submodule.coe_add, Pi.add_apply, add_mul]

omit hK in
theorem sectionForm_smul_left (c : ℂ) (f g : V) :
    sectionForm μ s ((c • f : V) : Y → ℂ) g = c * sectionForm μ s f g := by
  unfold sectionForm
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem sectionForm_add_right (f g g' : V) :
    sectionForm μ s f ((g + g' : V) : Y → ℂ) = sectionForm μ s f g + sectionForm μ s f g' := by
  rw [sectionForm_swap, hK.sectionForm_add_left, map_add, ← sectionForm_swap,
    ← sectionForm_swap]

omit hK in
theorem sectionForm_smul_right (c : ℂ) (f g : V) :
    sectionForm μ s f ((c • g : V) : Y → ℂ) = conj c * sectionForm μ s f g := by
  rw [sectionForm_swap, sectionForm_smul_left, map_mul, ← sectionForm_swap]

/-- `Re B(f, f) = ∫ |f(s x)|² dμ(x)`. -/
theorem re_sectionForm_self (f : V) :
    (sectionForm μ s f f).re = ∫ x, ‖(f : Y → ℂ) (s x)‖ ^ 2 ∂μ := by
  unfold sectionForm
  rw [← RCLike.re_eq_complex_re, ← integral_re (hK.integrable f f.2 f f.2)]
  congr 1
  funext x
  rw [RCLike.re_eq_complex_re, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem integrable_norm_sq (f : V) : Integrable (fun x => ‖(f : Y → ℂ) (s x)‖ ^ 2) μ := by
  refine ((hK.integrable f f.2 f f.2).re).congr (Filter.Eventually.of_forall fun x => ?_)
  change ((f : Y → ℂ) (s x) * conj ((f : Y → ℂ) (s x))).re = _
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem sectionForm_self_re_nonneg (f : V) : 0 ≤ (sectionForm μ s f f).re := by
  rw [hK.re_sectionForm_self]
  exact integral_nonneg fun x => sq_nonneg _

/-- The reproducing property in terms of `B`: `B(f, K y) = f(y)`. -/
theorem sectionForm_kernel (f : V) (y : Y) : sectionForm μ s f (K y) = (f : Y → ℂ) y :=
  hK.reproduce f f.2 y

end Form

/-- The space `V` with the inner product `⟪f, g⟫ = B(g, f) = ∫ conj(f(s x)) g(s x) dμ(x)`:
a type synonym of `V`, indexed by the hypothesis `hK`. -/
def Space (_ : IsSectionReproducingKernel μ s V K) : Type v := V

instance : AddCommGroup hK.Space := inferInstanceAs (AddCommGroup V)

instance : Module ℂ hK.Space := inferInstanceAs (Module ℂ V)

/-- The identity map `V → hK.Space`. -/
def toSpace : V ≃ₗ[ℂ] hK.Space := LinearEquiv.refl ℂ V

/-- The pre-inner product `⟪f, g⟫ = B(g, f)` on `hK.Space`. -/
@[instance_reducible]
def preCore : PreInnerProductSpace.Core ℂ hK.Space where
  inner f g := sectionForm μ s (hK.toSpace.symm g) (hK.toSpace.symm f)
  conj_inner_symm _ _ := (sectionForm_swap μ s _ _).symm
  re_inner_nonneg f := hK.sectionForm_self_re_nonneg (hK.toSpace.symm f)
  add_left f f' g :=
    hK.sectionForm_add_right (hK.toSpace.symm g) (hK.toSpace.symm f) (hK.toSpace.symm f')
  smul_left f g c := sectionForm_smul_right c (hK.toSpace.symm g) (hK.toSpace.symm f)

/-- The inner product core: the pre-inner product is definite by the reproducing property and
the Cauchy–Schwarz inequality, since `⟪K y, f⟫ = f(y)`. -/
@[instance_reducible]
def core : InnerProductSpace.Core ℂ hK.Space :=
  { hK.preCore with
    definite := fun f hf => by
      have hval : ∀ y, (hK.toSpace.symm f : Y → ℂ) y = 0 := by
        intro y
        have hcs := InnerProductSpace.Core.inner_mul_inner_self_le (c := hK.preCore)
          (hK.toSpace (K y)) f
        have h1 : hK.preCore.inner (hK.toSpace (K y)) f = (hK.toSpace.symm f : Y → ℂ) y :=
          hK.reproduce _ (hK.toSpace.symm f).2 y
        have h2 : hK.preCore.inner f (hK.toSpace (K y)) =
            conj ((hK.toSpace.symm f : Y → ℂ) y) := by
          rw [← h1]
          exact (hK.preCore.conj_inner_symm _ _).symm
        have h3 : hK.preCore.inner f f = 0 := hf
        change ‖hK.preCore.inner _ f‖ * ‖hK.preCore.inner f _‖ ≤
          RCLike.re (hK.preCore.inner _ _) * RCLike.re (hK.preCore.inner f f) at hcs
        rw [h1, h2, h3, map_zero, mul_zero, RCLike.norm_conj] at hcs
        exact norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) two_ne_zero).mp
          (le_antisymm (by rw [sq]; exact hcs) (sq_nonneg _)))
      exact hK.toSpace.symm.map_eq_zero_iff.mp (Subtype.ext (funext hval)) }

instance : NormedAddCommGroup hK.Space :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := hK.core)

instance : InnerProductSpace ℂ hK.Space :=
  InnerProductSpace.ofCore hK.core.toCore

theorem inner_toSpace (f g : V) :
    ⟪hK.toSpace f, hK.toSpace g⟫_ℂ = sectionForm μ s g f :=
  rfl

/-- The reproducing property in the inner product: `⟪K y, f⟫ = f(y)`. -/
theorem inner_toSpace_kernel (f : V) (y : Y) :
    ⟪hK.toSpace (K y), hK.toSpace f⟫_ℂ = (f : Y → ℂ) y :=
  hK.reproduce f f.2 y

theorem norm_toSpace_sq (f : V) :
    ‖hK.toSpace f‖ ^ 2 = ∫ x, ‖(f : Y → ℂ) (s x)‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toSpace, RCLike.re_to_complex, hK.re_sectionForm_self]

theorem norm_toSpace_kernel_sq (y : Y) : ‖hK.toSpace (K y)‖ ^ 2 = ((K y : Y → ℂ) y).re := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toSpace_kernel, RCLike.re_to_complex]

/-- Bessel's inequality at a point: if `e₁, …, eₙ ∈ V` are orthonormal for `⟪·, ·⟫`, then
`Σ |eᵢ(y)|² ≤ Re K(y)(y)`. -/
theorem sum_norm_sq_le {ι : Type*} (t : Finset ι) (e : ι → V)
    (he : Orthonormal ℂ (hK.toSpace ∘ e)) (y : Y) :
    ∑ i ∈ t, ‖(e i : Y → ℂ) y‖ ^ 2 ≤ ((K y : Y → ℂ) y).re := by
  rw [← hK.norm_toSpace_kernel_sq]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_)
    (he.sum_inner_products_le (hK.toSpace (K y)) (s := t))
  rw [Function.comp_apply, norm_inner_symm, hK.inner_toSpace_kernel]

/-- If `x ↦ Re K(s x)(s x)` is integrable, every orthonormal family of `n` elements of `V` has
`n ≤ ∫ Re K(s x)(s x) dμ(x)`. -/
theorem card_le_of_orthonormal (hint : Integrable (fun x => ((K (s x) : Y → ℂ) (s x)).re) μ)
    {n : ℕ} (e : Fin n → V) (he : Orthonormal ℂ (hK.toSpace ∘ e)) :
    (n : ℝ) ≤ ∫ x, ((K (s x) : Y → ℂ) (s x)).re ∂μ := by
  have hn : (n : ℝ) = ∑ i, ∫ x, ‖(e i : Y → ℂ) (s x)‖ ^ 2 ∂μ := by
    have h1 : ∀ i, ‖hK.toSpace (e i)‖ = 1 := fun i => he.1 i
    simp_rw [← hK.norm_toSpace_sq, h1]
    simp
  rw [hn, ← integral_finsetSum _ fun i _ => hK.integrable_norm_sq (e i)]
  exact integral_mono (integrable_finsetSum _ fun i _ => hK.integrable_norm_sq (e i)) hint
    (fun x => hK.sum_norm_sq_le Finset.univ e he (s x))

theorem finrank_le_of_submodule
    (hint : Integrable (fun x => ((K (s x) : Y → ℂ) (s x)).re) μ)
    (E : Submodule ℂ hK.Space) [FiniteDimensional ℂ E] :
    (finrank ℂ E : ℝ) ≤ ∫ x, ((K (s x) : Y → ℂ) (s x)).re ∂μ := by
  let b := stdOrthonormalBasis ℂ E
  refine hK.card_le_of_orthonormal hint (fun i => hK.toSpace.symm (b i : E)) ?_
  have h : (hK.toSpace ∘ fun i => hK.toSpace.symm (b i : E)) = E.subtypeₗᵢ ∘ b := by
    funext i
    simp
  rw [h]
  exact b.orthonormal.comp_linearIsometry E.subtypeₗᵢ

include hK in
/-- **Finite dimensionality** (Waldspurger, proof of Proposition VIII.4.1): if
`x ↦ Re K(s x)(s x)` is integrable, then `V` is finite dimensional. -/
theorem finiteDimensional (hint : Integrable (fun x => ((K (s x) : Y → ℂ) (s x)).re) μ) :
    FiniteDimensional ℂ V := by
  classical
  suffices FiniteDimensional ℂ hK.Space from LinearEquiv.finiteDimensional hK.toSpace.symm
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt
    (rank_le (n := ⌊∫ x, ((K (s x) : Y → ℂ) (s x)).re ∂μ⌋₊) fun t ht => ?_)
    Cardinal.natCast_lt_aleph0
  let E := Submodule.span ℂ (Set.range fun i : t => (i : hK.Space))
  have : FiniteDimensional ℂ E := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hcard : finrank ℂ E = t.card := by
    rw [finrank_span_eq_card ht]
    simp
  have h := hK.finrank_le_of_submodule hint E
  rw [hcard] at h
  exact Nat.le_floor h

include hK in
/-- The dimension bound `dim V ≤ ∫ Re K(s x)(s x) dμ(x)`. -/
theorem finrank_le (hint : Integrable (fun x => ((K (s x) : Y → ℂ) (s x)).re) μ) :
    (finrank ℂ V : ℝ) ≤ ∫ x, ((K (s x) : Y → ℂ) (s x)).re ∂μ := by
  have : FiniteDimensional ℂ V := hK.finiteDimensional hint
  have : FiniteDimensional ℂ hK.Space := LinearEquiv.finiteDimensional hK.toSpace
  have h := hK.finrank_le_of_submodule hint ⊤
  rwa [finrank_top, ← hK.toSpace.finrank_eq] at h

include hK in
/-- **Spanning** (Waldspurger, proof of Proposition VIII.4.1): under the integrability
hypothesis, `V` is spanned by the functions `K(y)`. -/
theorem span_kernel_eq_top (hint : Integrable (fun x => ((K (s x) : Y → ℂ) (s x)).re) μ) :
    Submodule.span ℂ (Set.range K) = ⊤ := by
  have : FiniteDimensional ℂ V := hK.finiteDimensional hint
  have : FiniteDimensional ℂ hK.Space := LinearEquiv.finiteDimensional hK.toSpace
  set F := Submodule.span ℂ (Set.range (hK.toSpace ∘ K))
  have hF : F = ⊤ := by
    refine (Submodule.orthogonal_eq_bot_iff (K := F)).1 ?_
    refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
    have h0 : ∀ y, (hK.toSpace.symm f : Y → ℂ) y = 0 := fun y => by
      have hy : hK.toSpace (K y) ∈ F := Submodule.subset_span ⟨y, rfl⟩
      have h := Submodule.inner_right_of_mem_orthogonal hy hf
      rwa [← hK.toSpace.apply_symm_apply f, hK.inner_toSpace_kernel] at h
    exact hK.toSpace.symm.map_eq_zero_iff.mp (Subtype.ext (funext h0))
  have h := congrArg (Submodule.map hK.toSpace.symm.toLinearMap) hF
  have hK' : (hK.toSpace.symm ∘ hK.toSpace ∘ K) = K :=
    funext fun y => hK.toSpace.symm_apply_apply (K y)
  rwa [Submodule.map_span, ← Set.range_comp, LinearEquiv.coe_coe, hK', Submodule.map_top,
    LinearEquiv.range] at h

/-- **Expansion of the kernel** (Waldspurger, proof of Proposition VIII.4.1): for an orthonormal
basis `(fᵢ)` of `V` for `⟪·, ·⟫`, `K(y)(y') = Σᵢ fᵢ(y') conj(fᵢ(y))`. -/
theorem kernel_apply_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ hK.Space)
    (y y' : Y) :
    (K y : Y → ℂ) y' = ∑ i, (hK.toSpace.symm (b i) : Y → ℂ) y' *
      conj ((hK.toSpace.symm (b i) : Y → ℂ) y) := by
  have h1 : ∀ i, ⟪b i, hK.toSpace (K y)⟫_ℂ = conj ((hK.toSpace.symm (b i) : Y → ℂ) y) := by
    intro i
    rw [← inner_conj_symm]
    conv_lhs => rw [← hK.toSpace.apply_symm_apply (b i)]
    rw [hK.inner_toSpace_kernel]
  have h := congrArg hK.toSpace.symm (b.sum_repr' (hK.toSpace (K y)))
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h, map_sum, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h1, mul_comm]

end IsSectionReproducingKernel

end Langlands.HarishChandraSchwartz
