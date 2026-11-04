import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff
import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.Jacquet.StablePairingProof
import Langlands.Representation.Character.TransportProof

/-! # Waldspurger's family `φ_H = φ ψ_H` in the proof of Proposition III.7.1

For an admissible representation `(ρ, E)` (Waldspurger's `ω̌`) and a compact open subgroup `H`,
`ψ_H(g) = trace[ρ(ε_H) ρ(g) ρ(ε_H)]` is the trace of the compressed action `e_H ρ(g)` on the
finite-dimensional space `E^H`. It is a coefficient of `ρ`, it satisfies
`ψ_{gHg⁻¹}(x) = ψ_H(g⁻¹ x g)` and, for `H ⊆ H'`, `(mes H')⁻¹ ∫_{H'} ψ_H(x k) dk = ψ_{H'}(x)`.

If the coefficients of `ρ` decrease rapidly on an open normal subgroup `N` containing every
compact open subgroup, with conjugation trivial on `G/N` (Waldspurger's `G¹`), then for every
compactly supported `φ` on `G/N` the functions `φ_H = ψ_H φ` lie in `C(G)` and form a family
with Waldspurger's properties (1) and (2), hence define the operators `π[φ]`.
-/

noncomputable section

universe u v w

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Plancherel (CoefficientTensor coefficientTensorMap coefficientTensorMap_tmul)

namespace Langlands.HarishChandraSchwartz

section TraceCoefficient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- Averaging over a compact open subgroup depends only on the subgroup. -/
theorem averageMap_congr (hρ : IsSmooth ρ) {K₁ K₂ : OpenSubgroup G} (h : K₁ = K₂)
    (h₁ : IsCompact (K₁ : Set G)) (h₂ : IsCompact (K₂ : Set G)) (v : V) :
    Compact.averageMap ρ hρ K₁ h₁ v = Compact.averageMap ρ hρ K₂ h₂ v := by
  subst h
  rfl

/-- The averaging projection `e_H : V → V^H` (the finite orbit mean `Compact.averageMap`). -/
def averageProjection (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G) :
    V →ₗ[ℂ] fixedVectors ρ H.toSubgroup :=
  (Compact.averageMap ρ hρ H.1 H.2).codRestrict (fixedVectors ρ H.toSubgroup)
    (Compact.averageMap_mem_fixedVectors ρ hρ H.1 H.2)

@[simp] theorem averageProjection_apply (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G) (v : V) :
    (averageProjection ρ hρ H v : V) = Compact.averageMap ρ hρ H.1 H.2 v :=
  rfl

/-- `e_H` is the identity on `V^H`. -/
theorem averageProjection_of_mem (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G)
    (w : fixedVectors ρ H.toSubgroup) : averageProjection ρ hρ H (w : V) = w :=
  Subtype.ext (Compact.averageMap_id ρ hρ H.1 H.2 w.val w.property)

/-- `e_H ρ(k) = e_H` for `k ∈ H`. -/
theorem averageProjection_rho_of_mem (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G) {k : G}
    (hk : k ∈ H.toSubgroup) (v : V) :
    averageProjection ρ hρ H (ρ k v) = averageProjection ρ hρ H v :=
  Subtype.ext (Jacquet.averageMap_apply_of_mem ρ hρ H.1 H.2 hk v)

/-- Waldspurger's `ψ_H(g) = trace[e_H ρ(g) e_H]`, computed as the trace of the compressed
action `e_H ρ(g)` on `V^H` (zero if `V^H` is infinite-dimensional). -/
def traceCoefficient (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G) (g : G) : ℂ :=
  LinearMap.trace ℂ (fixedVectors ρ H.toSubgroup) (Jacquet.compressedAction ρ hρ H.1 H.2 g)

/-- `ψ_H(g) = Σ_i b_i^*(e_H ρ(g) b_i)` for a basis `b` of `V^H`. -/
theorem traceCoefficient_eq_sum (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G)
    [FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ (fixedVectors ρ H.toSubgroup)) (g : G) :
    traceCoefficient ρ hρ H g = ∑ i, b.coord i (averageProjection ρ hρ H (ρ g (b i))) := by
  rw [traceCoefficient, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
  rfl

/-- The smooth functional `L ∘ e_H` on `V`, for a linear form `L` on `V^H`. -/
def fixedFunctional (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G)
    (L : Module.Dual ℂ (fixedVectors ρ H.toSubgroup)) : SmoothDual ρ :=
  ⟨L ∘ₗ averageProjection ρ hρ H, H.1, fun k => LinearMap.ext fun v => by
    change L (averageProjection ρ hρ H (ρ ((k : G)⁻¹) v)) = L (averageProjection ρ hρ H v)
    rw [averageProjection_rho_of_mem ρ hρ H (H.toSubgroup.inv_mem k.2)]⟩

/-- `ψ_{gHg⁻¹}(x) = ψ_H(g⁻¹ x g)`. -/
theorem traceCoefficient_conj (hρ : IsAdmissible ρ) (H : CompactOpenSubgroup G) (g x : G) :
    traceCoefficient ρ hρ.1 (H.conj g) x = traceCoefficient ρ hρ.1 H (g⁻¹ * x * g) := by
  have : FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup) := hρ.2 H.1
  have : FiniteDimensional ℂ (fixedVectors ρ (H.conj g).toSubgroup) := hρ.2 (H.conj g).1
  have hmem : ∀ w ∈ fixedVectors ρ (H.conj g).toSubgroup,
      ρ g⁻¹ w ∈ fixedVectors ρ H.toSubgroup := by
    intro w hw
    change ∀ h : H.toSubgroup, ρ (h : G) (ρ g⁻¹ w) = ρ g⁻¹ w
    intro h
    have hh : g * (h : G) * g⁻¹ ∈ (H.conj g).toSubgroup := by
      rw [CompactOpenSubgroup.conj_toSubgroup, mem_conjSubgroup]
      simp [mul_assoc]
    have h₁ : ρ (g * (h : G) * g⁻¹) w = w := hw ⟨_, hh⟩
    have h₂ : (h : G) * g⁻¹ = g⁻¹ * (g * (h : G) * g⁻¹) := by group
    rw [← Module.End.mul_apply, ← map_mul, h₂, map_mul, Module.End.mul_apply, h₁]
  let E : fixedVectors ρ H.toSubgroup →ₗ[ℂ] fixedVectors ρ (H.conj g).toSubgroup :=
    ((ρ g).comp (fixedVectors ρ H.toSubgroup).subtype).codRestrict _
      fun w => rho_mem_fixedVectors_conj w.2 g
  let F : fixedVectors ρ (H.conj g).toSubgroup →ₗ[ℂ] fixedVectors ρ H.toSubgroup :=
    (Jacquet.compressedAction ρ hρ.1 H.1 H.2 (g⁻¹ * x * g)).comp
      (((ρ g⁻¹).comp (fixedVectors ρ (H.conj g).toSubgroup).subtype).codRestrict _
        fun w => hmem w w.2)
  have hFE : F ∘ₗ E = Jacquet.compressedAction ρ hρ.1 H.1 H.2 (g⁻¹ * x * g) := by
    refine LinearMap.ext fun w => ?_
    have hw : (⟨ρ g⁻¹ (ρ g (w : V)), hmem _ (rho_mem_fixedVectors_conj w.2 g)⟩ :
        fixedVectors ρ H.toSubgroup) = w :=
      Subtype.ext (ρ.inv_self_apply g w)
    change Jacquet.compressedAction ρ hρ.1 H.1 H.2 (g⁻¹ * x * g)
      ⟨ρ g⁻¹ (ρ g (w : V)), hmem _ (rho_mem_fixedVectors_conj w.2 g)⟩ = _
    rw [hw]
  have hK : (H.conj g).1 = Jacquet.conjOpenSubgroup g H.1 := by
    ext y
    rw [Jacquet.mem_conjOpenSubgroup]
    exact mem_conjSubgroup
  have hK' : IsCompact (Jacquet.conjOpenSubgroup g H.1 : Set G) := hK ▸ (H.conj g).2
  have hEF : E ∘ₗ F = Jacquet.compressedAction ρ hρ.1 (H.conj g).1 (H.conj g).2 x := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ρ g (Compact.averageMap ρ hρ.1 H.1 H.2 (ρ (g⁻¹ * x * g) (ρ g⁻¹ (w : V)))) =
      Compact.averageMap ρ hρ.1 (H.conj g).1 (H.conj g).2 (ρ x w)
    have h₁ : ρ (g⁻¹ * x * g) (ρ g⁻¹ (w : V)) = ρ g⁻¹ (ρ x w) := by
      rw [map_mul, map_mul]
      simp only [Module.End.mul_apply, Representation.self_inv_apply]
    rw [h₁, ← Jacquet.averageMap_conj ρ hρ.1 g H.1 H.2 hK', Representation.self_inv_apply,
      averageMap_congr ρ hρ.1 hK]
  rw [traceCoefficient, traceCoefficient, ← hFE, ← hEF]
  exact (LinearMap.trace_comp_comm' E F).symm

end TraceCoefficient

section Coefficient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `ψ_H ∈ A(ρ)`: the function `ψ_H` is the coefficient of a tensor in `V ⊗ Ṽ`. -/
theorem traceCoefficient_mem_range (A : SmoothRep.{0, u, v} ℂ G)
    (hA : IsAdmissible A.representation) (H : CompactOpenSubgroup G) :
    ∃ f ∈ LinearMap.range (coefficientTensorMap A),
      ⇑f = traceCoefficient A.representation hA.1 H := by
  have : FiniteDimensional ℂ (fixedVectors A.representation H.toSubgroup) := hA.2 H.1
  classical
  let b := Module.finBasis ℂ (fixedVectors A.representation H.toSubgroup)
  let t : CoefficientTensor A := ∑ i, ((b i : A) ⊗ₜ[ℂ]
    fixedFunctional A.representation hA.1 H (b.coord i))
  refine ⟨coefficientTensorMap A t, LinearMap.mem_range_self _ _, ?_⟩
  funext g
  have h := map_sum ((LocallyConstant.evalₗ ℂ g).comp (coefficientTensorMap A))
    (fun i => (b i : A) ⊗ₜ[ℂ] fixedFunctional A.representation hA.1 H (b.coord i)) Finset.univ
  simp only [LinearMap.comp_apply, LocallyConstant.evalₗ_apply, coefficientTensorMap_tmul] at h
  rw [h, traceCoefficient_eq_sum A.representation hA.1 H b g]
  rfl

end Coefficient

section Measure

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

omit [BorelSpace G] in
/-- `k ↦ f(k) ℓ(ρ(k) v)` is integrable for a test function `f` and a smooth vector `v`. -/
theorem integrable_testFunction_mul_coefficient [OpensMeasurableSpace G]
    [IsFiniteMeasureOnCompacts μ] (hρ : IsSmooth ρ) (f : SchwartzBruhat G)
    (L : Module.Dual ℂ V) (v : V) : Integrable (fun k => f k * L (ρ k v)) μ := by
  have hc : Continuous (fun k => L (ρ k v)) :=
    (matrixCoefficient_isLocallyConstant ρ L v (hρ v)).continuous
  exact (f.continuous.mul hc).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

/-- For a left and right invariant Haar measure, the Hecke action of `ε_H = (mes H)⁻¹ 1_H` is
the averaging projection onto `V^H`. -/
theorem heckeAction_normalizedIndicator_eq_averageMap (hρ : IsSmooth ρ)
    (H : CompactOpenSubgroup G) (v : V) :
    Hecke.heckeAction μ ρ hρ (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) v =
      Compact.averageMap ρ hρ H.1 H.2 v := by
  have hinv : ∀ k : H.1, Hecke.heckeAction μ ρ hρ
      (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) (ρ k.val v) =
      Hecke.heckeAction μ ρ hρ (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) v := by
    intro k
    have hf : Hecke.TestFunction.rightTranslate (k.val⁻¹)
        (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2)) =
        Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) := by
      ext x
      rw [Hecke.TestFunction.rightTranslate_apply]
      exact (Hecke.HeckeAlgebra.normalizedIndicator_mem_biInvariant μ H.1 H.2).2
        ⟨k.val⁻¹, H.1.inv_mem k.2⟩ x
    rw [Hecke.heckeAction_apply, Hecke.heckeAction_apply,
      Character.integratedAction_right_input μ ρ hρ, hf]
  have h := Jacquet.map_averageMap_of_forall_eq ρ hρ H.1 H.2
    (Hecke.heckeAction μ ρ hρ (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2)) v _ hinv
  rw [Hecke.heckeAction_normalizedIndicator_of_fixed μ ρ hρ H.1 H.2
    (Compact.averageMap_mem_fixedVectors ρ hρ H.1 H.2 v)] at h
  exact h.symm

/-- `ρ(ε_H) = e_H` as an endomorphism of `V`. -/
theorem heckeAction_normalizedIndicator_eq_subtype_comp (hρ : IsSmooth ρ)
    (H : CompactOpenSubgroup G) :
    Hecke.heckeAction μ ρ hρ (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) =
      (fixedVectors ρ H.toSubgroup).subtype ∘ₗ averageProjection ρ hρ H :=
  LinearMap.ext fun v => heckeAction_normalizedIndicator_eq_averageMap μ ρ hρ H v

/-- The Library's `Hecke.fixedProjection` is the averaging projection `e_H`. -/
theorem fixedProjection_eq_averageProjection (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G) :
    Hecke.fixedProjection μ ρ hρ H.1 H.2 = averageProjection ρ hρ H :=
  LinearMap.ext fun v => Subtype.ext (heckeAction_normalizedIndicator_eq_averageMap μ ρ hρ H v)

/-- The operator `ρ(ε_H) ρ(g) ρ(ε_H)` of Waldspurger's `ψ_H` has finite rank. -/
theorem heckeAction_mul_rho_mul_heckeAction_mem (hρ : IsAdmissible ρ)
    (H : CompactOpenSubgroup G) (g : G) :
    Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) * ρ g *
        Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) ∈
      finiteRankEnd V := by
  have : FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup) := hρ.2 H.1
  have h : Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) * ρ g *
        Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) =
      (FiniteRankEnd.ofFactorization (averageProjection ρ hρ.1 H)
        ((fixedVectors ρ H.toSubgroup).subtype ∘ₗ averageProjection ρ hρ.1 H ∘ₗ ρ g ∘ₗ
          (fixedVectors ρ H.toSubgroup).subtype)).val := by
    rw [heckeAction_normalizedIndicator_eq_subtype_comp]
    exact LinearMap.ext fun _ => rfl
  rw [h]
  exact Subtype.property _

/-- Waldspurger's definition: `ψ_H(g)` is the trace of the finite-rank operator
`ρ(ε_H) ρ(g) ρ(ε_H)` on `V`. -/
theorem finiteRankTrace_eq_traceCoefficient (hρ : IsAdmissible ρ) (H : CompactOpenSubgroup G)
    (g : G) (T : finiteRankEnd V)
    (hT : T.val = Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2) *
      ρ g * Hecke.heckeAction μ ρ hρ.1 (Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2)) :
    FiniteRankEnd.trace T = traceCoefficient ρ hρ.1 H g := by
  have : FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup) := hρ.2 H.1
  rw [FiniteRankEnd.trace_eq_of_factorization T (averageProjection ρ hρ.1 H)
    ((fixedVectors ρ H.toSubgroup).subtype ∘ₗ averageProjection ρ hρ.1 H ∘ₗ ρ g ∘ₗ
      (fixedVectors ρ H.toSubgroup).subtype)
    (by rw [hT, heckeAction_normalizedIndicator_eq_subtype_comp]; exact LinearMap.ext fun _ => rfl)]
  rw [traceCoefficient]
  congr 1
  refine LinearMap.ext fun w => ?_
  change averageProjection ρ hρ.1 H (averageProjection ρ hρ.1 H (ρ g w) : V) = _
  rw [averageProjection_of_mem]
  rfl

/-- Waldspurger's property (2) for `ψ_H`: for `H ⊆ H'`,
`∫ ε_{H'}(k) ψ_H(x k) dk = ψ_{H'}(x)`. -/
theorem integral_normalizedIndicator_mul_traceCoefficient (hρ : IsAdmissible ρ)
    {H H' : CompactOpenSubgroup G} (hHH' : H.toSubgroup ≤ H'.toSubgroup) (x : G) :
    ∫ k, (Hecke.HeckeAlgebra.normalizedIndicator μ H'.1 H'.2 : SchwartzBruhat G) k *
        traceCoefficient ρ hρ.1 H (x * k) ∂μ = traceCoefficient ρ hρ.1 H' x := by
  have : FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup) := hρ.2 H.1
  have : FiniteDimensional ℂ (fixedVectors ρ H'.toSubgroup) := hρ.2 H'.1
  classical
  set ε : SchwartzBruhat G :=
    (Hecke.HeckeAlgebra.normalizedIndicator μ H'.1 H'.2 : SchwartzBruhat G) with hε
  let b := Module.finBasis ℂ (fixedVectors ρ H.toSubgroup)
  let L : Fin (Module.finrank ℂ (fixedVectors ρ H.toSubgroup)) → Module.Dual ℂ V :=
    fun i => b.coord i ∘ₗ averageProjection ρ hρ.1 H ∘ₗ ρ x
  have hsum : ∀ k, ε k * traceCoefficient ρ hρ.1 H (x * k) = ∑ i, ε k * L i (ρ k (b i)) := by
    intro k
    rw [traceCoefficient_eq_sum ρ hρ.1 H b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Module.End.mul_apply]
    rfl
  have hint : ∀ i, ∫ k, ε k * L i (ρ k (b i)) ∂μ =
      b.coord i (averageProjection ρ hρ.1 H (ρ x (Compact.averageMap ρ hρ.1 H'.1 H'.2 (b i)))) := by
    intro i
    rw [← Hecke.integratedAction_dual μ ρ hρ.1 ε (b i) (L i)]
    have h2 : Hecke.integratedAction μ ρ hρ.1 ε (b i) =
        Compact.averageMap ρ hρ.1 H'.1 H'.2 (b i) :=
      heckeAction_normalizedIndicator_eq_averageMap μ ρ hρ.1 H' (b i)
    rw [h2]
    rfl
  simp_rw [hsum]
  rw [integral_finsetSum _ fun i _ => integrable_testFunction_mul_coefficient μ ρ hρ.1 ε (L i) _]
  simp_rw [hint]
  let E : fixedVectors ρ H.toSubgroup →ₗ[ℂ] fixedVectors ρ H'.toSubgroup :=
    averageProjection ρ hρ.1 H' ∘ₗ (fixedVectors ρ H.toSubgroup).subtype
  let F : fixedVectors ρ H'.toSubgroup →ₗ[ℂ] fixedVectors ρ H.toSubgroup :=
    averageProjection ρ hρ.1 H ∘ₗ ρ x ∘ₗ (fixedVectors ρ H'.toSubgroup).subtype
  have hM : LinearMap.trace ℂ _ (F ∘ₗ E) = ∑ i, b.coord i (averageProjection ρ hρ.1 H
      (ρ x (Compact.averageMap ρ hρ.1 H'.1 H'.2 (b i)))) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
    rfl
  have hEF : E ∘ₗ F = Jacquet.compressedAction ρ hρ.1 H'.1 H'.2 x := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact Jacquet.averageMap_averageMap_of_le ρ hρ.1 H'.1 H.1 H'.2 H.2
      (OpenSubgroup.toSubgroup_le.mp hHH') (ρ x w)
  rw [← hM, LinearMap.trace_comp_comm', hEF]
  rfl

end Measure

section Family

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hA : IsAdmissible A.representation)
  {N : Subgroup G} [N.Normal]

/-- Waldspurger's `φ_H = φ ψ_H ∈ C(G)`, for `φ` compactly supported on `G/N` and coefficients
of `A` decreasing rapidly on `N`. -/
def traceCutoff (ht : TranslationWeights Ξ σ) (hN : IsOpen (N : Set G))
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation) {φ : G ⧸ N → ℂ}
    (hφ : HasCompactSupport φ) (H : CompactOpenSubgroup G) : Space Ξ σ :=
  (⟨fun g => traceCoefficient A.representation hA.1 H g * φ g, by
    obtain ⟨f, hf, hfeq⟩ := traceCoefficient_mem_range A hA H
    have h := ht.mul_mem_schwartzSubmodule hN hD hf hφ
    rwa [hfeq] at h⟩ : schwartzSubmodule Ξ σ)

theorem traceCutoff_apply (ht : TranslationWeights Ξ σ) (hN : IsOpen (N : Set G))
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation) {φ : G ⧸ N → ℂ}
    (hφ : HasCompactSupport φ) (H : CompactOpenSubgroup G) (g : G) :
    traceCutoff A hA ht hN hD hφ H g = traceCoefficient A.representation hA.1 H g * φ g :=
  rfl

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant]
  {K : Subgroup G} [CompactSpace K]

/-- Waldspurger's family `H ↦ φ_H = φ ψ_H`, with properties (1) and (2) of the proof of
Proposition III.7.1. Here `N` is open and normal, contains every compact open subgroup, and
conjugation acts trivially on `G/N` (as for `N = G¹`). -/
def traceFamily (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ)
    (hN : IsOpen (N : Set G)) (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation)
    (hconj : ∀ g x : G, ((g⁻¹ * x * g : G) : G ⧸ N) = (x : G ⧸ N))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ N) {φ : G ⧸ N → ℂ}
    (hφ : HasCompactSupport φ) : IdempotentFamily hc ht where
  toFun := traceCutoff A hA ht hN hD hφ
  convolution_normalizedIndicator H H' hHH' := Space.ext fun x => by
    change HarishChandraSchwartz.convolution μ (traceCutoff A hA ht hN hD hφ H)
      (Space.normalizedIndicator μ hc.continuous_xi hc.pos hc.continuous_sigma hc.nonneg H') x =
      traceCutoff A hA ht hN hD hφ H' x
    rw [convolution_apply]
    have hpt : ∀ k, traceCutoff A hA ht hN hD hφ H (x * k) *
        Space.normalizedIndicator μ hc.continuous_xi hc.pos hc.continuous_sigma hc.nonneg H'
          ((x * k)⁻¹ * x) =
        (Hecke.HeckeAlgebra.normalizedIndicator μ H'.1 H'.2 : SchwartzBruhat G) k *
          traceCoefficient A.representation hA.1 H (x * k) * φ x := by
      intro k
      rw [traceCutoff_apply, Space.normalizedIndicator_apply, show (x * k)⁻¹ * x = k⁻¹ by group]
      change _ = (μ.real (H'.1 : Set G) : ℂ)⁻¹ * (H'.1 : Set G).indicator (fun _ => (1 : ℂ)) k *
        _ * _
      by_cases hk : k ∈ (H'.1 : Set G)
      · have hk' : k⁻¹ ∈ (H'.1 : Set G) := H'.1.inv_mem hk
        rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk',
          QuotientGroup.mk_mul_of_mem x (hHN H' hk)]
        ring
      · have hk' : k⁻¹ ∉ (H'.1 : Set G) := fun h => hk (by simpa using H'.1.inv_mem h)
        rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk']
        ring
    calc ∫ y, traceCutoff A hA ht hN hD hφ H y *
          Space.normalizedIndicator μ hc.continuous_xi hc.pos hc.continuous_sigma hc.nonneg H'
            (y⁻¹ * x) ∂μ
        = ∫ k, traceCutoff A hA ht hN hD hφ H (x * k) *
          Space.normalizedIndicator μ hc.continuous_xi hc.pos hc.continuous_sigma hc.nonneg H'
            ((x * k)⁻¹ * x) ∂μ :=
          (integral_mul_left_eq_self (fun y => traceCutoff A hA ht hN hD hφ H y *
            Space.normalizedIndicator μ hc.continuous_xi hc.pos hc.continuous_sigma hc.nonneg H'
              (y⁻¹ * x)) x).symm
      _ = ∫ k, (Hecke.HeckeAlgebra.normalizedIndicator μ H'.1 H'.2 : SchwartzBruhat G) k *
          traceCoefficient A.representation hA.1 H (x * k) * φ x ∂μ := by
          congr 1
          funext k
          exact hpt k
      _ = (∫ k, (Hecke.HeckeAlgebra.normalizedIndicator μ H'.1 H'.2 : SchwartzBruhat G) k *
          traceCoefficient A.representation hA.1 H (x * k) ∂μ) * φ x := integral_mul_const _ _
      _ = traceCutoff A hA ht hN hD hφ H' x := by
          rw [integral_normalizedIndicator_mul_traceCoefficient μ A.representation hA hHH',
            traceCutoff_apply]
  translate_conj g H := Space.ext fun x => by
    change traceCutoff A hA ht hN hD hφ H (g⁻¹ * x * g) = traceCutoff A hA ht hN hD hφ (H.conj g) x
    rw [traceCutoff_apply, traceCutoff_apply, traceCoefficient_conj A.representation hA H g x,
      hconj g x]

theorem traceFamily_toFun (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ)
    (hN : IsOpen (N : Set G)) (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation)
    (hconj : ∀ g x : G, ((g⁻¹ * x * g : G) : G ⧸ N) = (x : G ⧸ N))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ N) {φ : G ⧸ N → ℂ}
    (hφ : HasCompactSupport φ) (H : CompactOpenSubgroup G) :
    (traceFamily A hA hc ht hN hD hconj hHN hφ).toFun H = traceCutoff A hA ht hN hD hφ H :=
  rfl

variable {W : Type w} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G W}

/-- The first equality in Waldspurger's computation of `π[φ]`: for `H` fixing `v` and a smooth
functional `ℓ`, `ℓ(π[φ] v) = ∫_G ψ_H(g) φ(g) ℓ(π(g) v) dg`. -/
theorem traceFamily_operator_eval (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ)
    (hN : IsOpen (N : Set G)) (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation)
    (hconj : ∀ g x : G, ((g⁻¹ * x * g : G) : G ⧸ N) = (x : G ⧸ N))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ N) {φ : G ⧸ N → ℂ}
    (hφ : HasCompactSupport φ) (hw : L2Weights μ Ξ σ) (hπ : IsAdmissible π)
    (hT : HasTemperedCoefficients Ξ σ π) {H : CompactOpenSubgroup G} {v : W}
    (hv : v ∈ fixedVectors π H.toSubgroup) (ℓ : SmoothDual π) :
    ℓ.val ((traceFamily A hA hc ht hN hD hconj hHN hφ).operator hw hπ hT v) =
      ∫ g, traceCoefficient A.representation hA.1 H g * φ g * ℓ.val (π g v) ∂μ := by
  rw [IdempotentFamily.operator_apply_of_mem _ hw hπ hT hv, schwartzAction_eval]
  rfl

end Family

end Langlands.HarishChandraSchwartz
