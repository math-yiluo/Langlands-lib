import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedCoefficientSmoothness
import Langlands.HarmonicAnalysis.TorusFourierInversion

/-! # Smoothness of `π(f χ)` along a torus of characters (Waldspurger VII.1.3, case `M = G`)

Waldspurger, proof of Proposition VII.1.3 (printed p. 316): after reduction to `M = G` by Lemma
VII.1.2, for `v ∈ E^H`, `v̌ ∈ Ě^H`, `f ∈ C_H` and `χ ∈ Im X(G)`, the function
`C_{v⊗v̌, f}(χ) = d(ω ⊗ χ) ⟨(ω ⊗ χ)(f̌) v, v̌⟩` is smooth on `Im X(G)`.

Here `Im X(G)` is replaced by a finite torus `J → Circle` and `χ(g)` by
`χ_z(g) = ∏ⱼ zⱼ^{n(g)ⱼ}` for a supplied map `n : G → (J → ℤ)` that is additive, vanishes on a
compact open subgroup, is measurable and satisfies `‖n(g)‖ ≤ C (1 + σ(g))`. Since
`(ω ⊗ χ)(f) = ω(f χ)`, the operator is `π(f χ_z)` for the twist `Space.twist … z f` of `f`.
`schwartzActionTensor_eq_sum` writes the tensor of `π(f)` in a basis of `A^K` with coefficients
`ℓ_j(π(f) b_i)`; for `f χ_z` these coefficients are the twisted coefficients of
`TwistedCoefficientSmoothness` (`smoothDual_schwartzAction_twist`). Hence
`z ↦ π(f χ_z) ∈ A ⊗ Ã` is a finite smooth family
(`schwartzActionTensor_twist_mem_finiteSmoothFamilies`).
-/

noncomputable section

open MeasureTheory Filter Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped ComplexConjugate NNReal ENNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe u v

section Twist

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Ξ σ : G → ℝ} {J : Type*} [Fintype J] {n : G → J → ℤ}

/-- The twist `g ↦ f(g) χ_z(g)` of a function by the character `χ_z(g) = ∏ⱼ zⱼ^{n(g)ⱼ}`. -/
def twistedFunction (n : G → J → ℤ) (z : J → Circle) (f : G → ℂ) : G → ℂ :=
  fun g => f g * torusCharacter (n g) z

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nu_twistedFunction (z : J → Circle) (r : ℝ) (f : G → ℂ) :
    nu Ξ σ r (twistedFunction n z f) = nu Ξ σ r f := by
  unfold nu twistedFunction
  refine iSup_congr fun g => ?_
  rw [enorm_mul, ← ofReal_norm (torusCharacter (n g) z), norm_torusCharacter,
    ENNReal.ofReal_one, mul_one]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem IsBiInvariant.twistedFunction (hn : ∀ g h, n (g * h) = n g + n h) {H : Subgroup G}
    (hH : ∀ k ∈ H, n k = 0) (z : J → Circle) {f : G → ℂ} (hf : IsBiInvariant H f) :
    IsBiInvariant H (twistedFunction n z f) := by
  intro k₁ hk₁ k₂ hk₂ g
  simp only [HarishChandraSchwartz.twistedFunction]
  rw [hf k₁ hk₁ k₂ hk₂ g, hn, hn, hH k₁ hk₁, hH k₂ hk₂, zero_add, add_zero]

variable [Nonempty (CompactOpenSubgroup G)]

/-- If `n` is additive and vanishes on a compact open subgroup `K₀`, the twist of `f ∈ C(G)` lies
in `C(G)`; it is bi-invariant under `H ∩ K₀` whenever `f` is bi-invariant under `H`. -/
theorem twistedFunction_mem_schwartzSubmodule (hn : ∀ g h, n (g * h) = n g + n h)
    {K₀ : CompactOpenSubgroup G} (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (z : J → Circle)
    {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) :
    twistedFunction n z f ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  refine (mem_schwartzSubmodule_iff Ξ σ).mpr ⟨H.inf K₀, ?_, fun r => ?_⟩
  · exact (hH.1.mono (CompactOpenSubgroup.inf_le_left H K₀)).twistedFunction hn
      (fun k hk => hK₀ k (CompactOpenSubgroup.inf_le_right H K₀ hk)) z
  · rw [nu_twistedFunction]
    exact hH.2 r

/-- The twist `f ↦ f χ_z` as a linear map on `C(G)`. -/
def Space.twist (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup G}
    (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (z : J → Circle) : Space Ξ σ →ₗ[ℂ] Space Ξ σ where
  toFun f := ⟨twistedFunction n z f,
    twistedFunction_mem_schwartzSubmodule hn hK₀ z (Space.coe_mem f)⟩
  map_add' f₁ f₂ := Space.ext fun g => by
    change (f₁ g + f₂ g) * torusCharacter (n g) z =
      f₁ g * torusCharacter (n g) z + f₂ g * torusCharacter (n g) z
    ring
  map_smul' c f := Space.ext fun g => by
    change (c * f g) * torusCharacter (n g) z = c * (f g * torusCharacter (n g) z)
    ring

theorem Space.twist_apply (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup G}
    (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (z : J → Circle) (f : Space Ξ σ) (g : G) :
    Space.twist hn hK₀ z f g = f g * torusCharacter (n g) z :=
  rfl

end Twist

section Tensor

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)

omit [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- A vector of `A^K` is recovered from the values of the fixed functionals of a basis of
`A^K`. -/
theorem sum_fixedFunctional_smul {K : CompactOpenSubgroup G} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (fixedVectors A.representation K.toSubgroup)) {x : A}
    (hx : x ∈ fixedVectors A.representation K.toSubgroup) :
    ∑ j, (fixedFunctional A.representation hA.1 K (b.coord j)).val x • (b j : A) = x := by
  have h : ∀ j, (fixedFunctional A.representation hA.1 K (b.coord j)).val x =
      b.coord j ⟨x, hx⟩ := fun j => by
    change b.coord j (averageProjection A.representation hA.1 K x) = _
    rw [averageProjection_of_mem A.representation hA.1 K ⟨x, hx⟩]
  simp only [h]
  have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  rw [Submodule.coe_sum] at this
  simpa only [Module.Basis.coord_apply, Submodule.coe_smul] using this

/-- **Coordinates of `π(f)` as a tensor**: if `f` is bi-invariant under `K` and `b` is a basis
of `A^K`, then `π(f) = Σ_{i,j} ℓ_j(π(f) b_i) b_j ⊗ ℓ_i` in `A ⊗ Ã`, where `ℓ_i` is the smooth
functional `b.coord i ∘ e_K`. -/
theorem schwartzActionTensor_eq_sum {K : CompactOpenSubgroup G} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (fixedVectors A.representation K.toSubgroup)) {f : Space Ξ σ}
    (hf : IsBiInvariant K.toSubgroup f) :
    schwartzActionTensor A hw hA hT f =
      ∑ i, ∑ j, (fixedFunctional A.representation hA.1 K (b.coord j)).val
          (schwartzAction hw hA hT f (b i)) •
        ((b j : A) ⊗ₜ[ℂ] fixedFunctional A.representation hA.1 K (b.coord i)) := by
  refine schwartzActionTensor_eq_of_coefficientTensorToEnd_eq A hw hA hT ?_
  refine LinearMap.ext fun w => ?_
  have hleft : ∀ h ∈ K.toSubgroup, ∀ g, f (h * g) = f g := fun h hh g => by
    have h₁ := hf h hh 1 (one_mem _) g
    rwa [mul_one] at h₁
  have hright : ∀ k ∈ K.toSubgroup, ∀ g, f (g * k) = f g := fun k hk g => by
    have h₁ := hf 1 (one_mem _) k hk g
    rwa [one_mul] at h₁
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    coefficientTensorToEnd_tmul]
  have hinner : ∀ i, ∑ j, (fixedFunctional A.representation hA.1 K (b.coord j)).val
      (schwartzAction hw hA hT f (b i)) •
        (fixedFunctional A.representation hA.1 K (b.coord i)).val w • (b j : A) =
      (fixedFunctional A.representation hA.1 K (b.coord i)).val w •
        schwartzAction hw hA hT f (b i) := fun i => by
    simp_rw [smul_comm _ ((fixedFunctional A.representation hA.1 K (b.coord i)).val w)]
    rw [← Finset.smul_sum, sum_fixedFunctional_smul A hA b
      (schwartzAction_mem_fixedVectors hw hA hT hleft _)]
  simp_rw [hinner]
  have hsum : ∑ i, (fixedFunctional A.representation hA.1 K (b.coord i)).val w •
      schwartzAction hw hA hT f (b i) =
      schwartzAction hw hA hT f (averageProjection A.representation hA.1 K w : A) := by
    conv_rhs => rw [← b.sum_repr (averageProjection A.representation hA.1 K w)]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, map_smul]
    rfl
  rw [hsum, averageProjection_apply]
  exact Jacquet.map_averageMap_of_forall_eq A.representation hA.1 K.1 K.2
    (schwartzAction hw hA hT f) w _
    fun k => schwartzAction_apply_rho_of_mem A hw hA hT hright k.2 w

end Tensor

section Family

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)
  {J : Type*} [Fintype J] {n : G → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h)
  {K₀ : CompactOpenSubgroup G} (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n)
  {C : ℝ} (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g))

omit [μ.IsMulRightInvariant] in
/-- The coefficients of `π(f χ_z)` are the twisted coefficients of `f`:
`ℓ(π(f χ_z) v) = ∫_G f(g) ℓ(π(g) v) χ_z(g) dμ(g)`, a smooth function of `z`. -/
theorem smoothDual_schwartzAction_twist (f : Space Ξ σ) (w : A) (ℓ : SmoothDual A.representation)
    (z : J → Circle) :
    ℓ.val (schwartzAction hw hA hT (Space.twist hn hK₀ z f) w) =
      (twistedCoefficientFamily hw hnm hnσ (continuous_coefficient hA.1 w ℓ)
        (exists_nu_coefficient_ne_top hw hT w ℓ).choose_spec f : (J → Circle) → ℂ) z := by
  rw [schwartzAction_eval, twistedCoefficientFamily_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  change f g * torusCharacter (n g) z * ℓ.val (A.representation g w) =
    f g * ℓ.val (A.representation g w) * torusCharacter (n g) z
  ring

include hnm hnσ in
/-- **Smoothness of `π(f χ_z)` in `z`** (the core of Waldspurger's Proposition VII.1.3 for
`M = G`, in torus coordinates): the family `z ↦ π(f χ_z) ∈ A ⊗ Ã` is a finite smooth family on
`J → Circle`, for `χ_z(g) = ∏ⱼ zⱼ^{n(g)ⱼ}` with `n` additive, vanishing on a compact open
subgroup, measurable and of linear growth in `σ`. -/
theorem schwartzActionTensor_twist_mem_finiteSmoothFamilies (f : Space Ξ σ) :
    (fun z => schwartzActionTensor A hw hA hT (Space.twist hn hK₀ z f)) ∈
      finiteSmoothFamilies J (CoefficientTensor A) := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  let K := H.inf K₀
  have hK : ∀ z, IsBiInvariant K.toSubgroup (Space.twist hn hK₀ z f : G → ℂ) := fun z =>
    (hH.1.mono (CompactOpenSubgroup.inf_le_left H K₀)).twistedFunction hn
      (fun k hk => hK₀ k (CompactOpenSubgroup.inf_le_right H K₀ hk)) z
  have : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) := hA.2 K.1
  let b := Module.finBasis ℂ (fixedVectors A.representation K.toSubgroup)
  let ℓ : Fin (Module.finrank ℂ (fixedVectors A.representation K.toSubgroup)) →
      SmoothDual A.representation := fun i => fixedFunctional A.representation hA.1 K (b.coord i)
  have heq : (fun z => schwartzActionTensor A hw hA hT (Space.twist hn hK₀ z f)) =
      ∑ i, ∑ j, fun z => (ℓ j).val (schwartzAction hw hA hT (Space.twist hn hK₀ z f) (b i)) •
        ((b j : A) ⊗ₜ[ℂ] ℓ i) := by
    funext z
    rw [schwartzActionTensor_eq_sum A hw hA hT b (hK z)]
    simp only [Finset.sum_apply]
    rfl
  rw [heq]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  refine Submodule.subset_span ⟨twistedCoefficientFamily hw hnm hnσ
    (continuous_coefficient hA.1 (b i) (ℓ j))
    (exists_nu_coefficient_ne_top hw hT (b i) (ℓ j)).choose_spec f, (b j : A) ⊗ₜ[ℂ] ℓ i, ?_⟩
  funext z
  rw [smoothDual_schwartzAction_twist A hw hA hT hn hK₀ hnm hnσ]

end Family

end Langlands.HarishChandraSchwartz
