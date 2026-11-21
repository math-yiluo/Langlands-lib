import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Group.Integral

/-! # Compact convolution coordinates by finite sums of evaluations -/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

section Compact

variable {K G E : Type*}
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [Group G] [AddCommGroup E] [Module ℂ E]

/-- A finite sum of products for the kernel of a compact convolution. -/
def HasFiniteCompactConvolutionKernel (κ : K → ℂ) : Prop :=
  ∃ (m : ℕ) (α β : Fin m → K → ℂ),
    (∀ j, Continuous (β j)) ∧ ∀ x k, κ (x⁻¹ * k) = ∑ j, α j x * β j k

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] in
theorem hasFiniteCompactConvolutionKernel_of_finite_translates (κ : K → ℂ) (hκ : Continuous κ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k)))) :
    HasFiniteCompactConvolutionKernel κ := by
  let V := Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k))
  let : FiniteDimensional ℂ V := hfin
  let b := Module.finBasis ℂ V
  let shift (x : K) : V := ⟨fun k => κ (x⁻¹ * k), Submodule.subset_span ⟨x, rfl⟩⟩
  have hcont (v : V) : Continuous v.val := by
    refine Submodule.span_induction (p := fun f _ => Continuous f) ?_ continuous_const ?_ ?_ v.2
    · rintro _ ⟨x, rfl⟩
      exact hκ.comp (continuous_const.mul continuous_id)
    · intro _ _ _ _ h h'
      exact h.add h'
    · intro c _ _ h
      exact continuous_const.smul h
  refine ⟨Module.finrank ℂ V, fun j x => b.repr (shift x) j, fun j => (b j).val,
    fun j => hcont (b j), ?_⟩
  intro x k
  have hb := congrArg (fun v : V => v.val k) (b.sum_repr (shift x))
  simpa only [shift, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using hb.symm

omit [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] in
/-- A linear form on a finite-dimensional space of functions is a finite sum of evaluations. -/
theorem linearForm_eq_finitelyManyEvaluations
    [FiniteDimensional ℂ E] (ρ : E →ₗ[ℂ] (K → ℂ)) (hρ : Function.Injective ρ) (ℓ : E →ₗ[ℂ] ℂ) :
    ∃ c : K →₀ ℂ, ∀ v : E, ℓ v = ∑ x ∈ c.support, c x * ρ v x := by
  classical
  let ev (x : K) := (LinearMap.proj x).comp ρ
  have hker : (⨅ x, LinearMap.ker (ev x)) ≤ LinearMap.ker ℓ := by
    intro v hv
    have hv0 : v = 0 := hρ (funext fun x => by
      have hx := (Submodule.mem_iInf _).mp hv x
      simpa [ev] using LinearMap.mem_ker.mp hx)
    simp [hv0]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  refine ⟨c, fun v => ?_⟩
  have hv := congrArg (fun L : E →ₗ[ℂ] ℂ => L v) hc
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, ev, smul_eq_mul] using hv.symm

omit [T2Space K] in
/-- A compact convolution whose translates lie in the given function space has
finite-rank coordinates expressed by continuous compact pairings. -/
theorem exists_compactPairing_expansion
    (μ : Measure K) [μ.IsHaarMeasure] (iK : K →* G)
    (f : G → ℂ) (hf : ∀ g : G, Continuous fun k : K => f (iK k * g))
    (κ : K → ℂ) (hκ : Continuous κ) (hκfin : HasFiniteCompactConvolutionKernel κ)
    (ρ : E →ₗ[ℂ] (K → ℂ)) (hρ : Function.Injective ρ) (p : G → E)
    (hp : ∀ (g : G) (x : K), ρ (p g) x = ∫ k, κ k * f (iK x * iK k * g) ∂μ) :
    ∃ (m : ℕ) (v : Fin m → E) (κ' : Fin m → K → ℂ), (∀ j, Continuous (κ' j)) ∧
      ∀ g, p g = ∑ j, (∫ k, κ' j k * f (iK k * g) ∂μ) • v j := by
  classical
  obtain ⟨d, α, β, hβ, hExp⟩ := hκfin
  have hshift (g : G) (x : K) : ρ (p g) x = ∫ k, κ (x⁻¹ * k) * f (iK k * g) ∂μ := by
    rw [hp, ← integral_mul_left_eq_self (fun k : K => κ (x⁻¹ * k) * f (iK k * g)) x]
    simp only [inv_mul_cancel_left, map_mul]
  let V := Submodule.span ℂ (Set.range p)
  let W := Submodule.span ℂ (Set.range α)
  have hW (g : G) : ρ (p g) ∈ W := by
    have hsum : ρ (p g) = ∑ j, (∫ k, β j k * f (iK k * g) ∂μ) • α j := by
      funext x
      rw [hshift]
      simp_rw [hExp, Finset.sum_mul]
      rw [integral_finsetSum]
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [mul_assoc, integral_const_mul]
        exact mul_comm _ _
      · intro j _
        exact ((continuous_const.mul (hβ j)).mul (hf g)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [hsum]
    exact W.sum_mem fun j _ => W.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hV : V ≤ W.comap ρ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hW g
  let ρW := (ρ.comp V.subtype).codRestrict W (fun v => hV v.2)
  have hρW : Function.Injective ρW := fun _ _ h => Subtype.ext (hρ (congrArg Subtype.val h))
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range α)
  let : FiniteDimensional ℂ V := FiniteDimensional.of_injective ρW hρW
  let b := Module.finBasis ℂ V
  obtain ⟨w, hw⟩ : ∃ w : Fin (Module.finrank ℂ V) → K →₀ ℂ,
      ∀ j v, b.coord j v = ∑ x ∈ (w j).support, w j x * ρ v.val x := by
    have hR : Function.Injective (ρ.comp V.subtype) := hρ.comp Subtype.val_injective
    choose w hw using fun j => linearForm_eq_finitelyManyEvaluations (ρ.comp V.subtype) hR (b.coord j)
    exact ⟨w, hw⟩
  let ψ (j : Fin (Module.finrank ℂ V)) (k : K) := ∑ x ∈ (w j).support, w j x * κ (x⁻¹ * k)
  refine ⟨Module.finrank ℂ V, fun j => (b j).val, ψ, ?_, ?_⟩
  · intro j
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hκ.comp (continuous_const.mul continuous_id))
  · intro g
    let pg : V := ⟨p g, Submodule.subset_span ⟨g, rfl⟩⟩
    have hcoord (j : Fin (Module.finrank ℂ V)) :
        b.coord j pg = ∫ k, ψ j k * f (iK k * g) ∂μ := by
      rw [hw j pg]
      change (∑ x ∈ (w j).support, w j x * ρ (p g) x) = _
      simp_rw [hshift]
      unfold ψ
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun x _ => by simp only [mul_assoc, integral_const_mul]
      · intro x _
        exact ((continuous_const.mul (hκ.comp (continuous_const.mul continuous_id))).mul
          (hf g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hB := congrArg Subtype.val (b.sum_repr pg)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, ← Module.Basis.coord_apply, hcoord, pg] using hB.symm

end Compact

section ComplexPrincipalSeries

open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => GeneralLinear.inverseTranspose n ℂ
local notation "wd" => ArchimedeanLocal.dualFunction n

local instance complexCompactProjectionMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℂ j) := borel _
local instance complexCompactProjectionBorel (j : ℕ) :
    BorelSpace (unitaryCompact ℂ j) := ⟨rfl⟩

variable (r) in
/-- A compact convolution formula on inducing vectors and compatibility with the
Whittaker map give paired finite Whittaker and matrix-coefficient expansions. -/
def ComplexLocalCompactProjectionReductionStatement : Prop :=
  ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (μ : Measure Kc), μ.IsHaarMeasure →
  ∀ (κ : Kc → ℂ), Continuous κ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x : Kc => fun k => κ (x⁻¹ * k))) →
  ∀ (f : complexStandardKFinite n ds)
    (B : complexStandardKFinite n ds →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∀ (p : G → complexStandardKFinite n ds),
    (∀ (g : G) (x : Kc), (p g : G → ℂ) x.val =
      ∫ k, κ k * (f : G → ℂ) (x.val * k.val * g) ∂μ) →
    (∀ x g : G, B (p g) x = ∫ k, κ k * B f (x * k.val * g) ∂μ) →
    ∃ (m : ℕ) (W : Fin m → G → ℂ) (κ' : Fin m → Kc → ℂ),
      (∀ j, W j ∈ complexWhittakerModel r ds a ∧ Continuous (κ' j)) ∧
      ∀ x g : G,
        (∫ k, κ k * B f (x * k.val * g) ∂μ) =
          ∑ j, W j x * (∫ k, κ' j k * (f : G → ℂ) (k.val * g) ∂μ) ∧
        (∫ k, κ k * wd (B f) (x * ι k.val * g) ∂μ) =
          ∑ j, wd (W j) x * (∫ k, κ' j k * (f : G → ℂ) (k.val * ι g) ∂μ)

set_option backward.isDefEq.respectTransparency false in
theorem complexLocalCompactProjectionReduction : ComplexLocalCompactProjectionReductionStatement r := by
  intro ds a μ hμ κ hκ hκfin f B hB p hp hProj
  let : μ.IsHaarMeasure := hμ
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  let E := complexStandardKFinite n ds
  let ρ : E →ₗ[ℂ] (Kc → ℂ) :=
    { toFun := fun v k => (v : G → ℂ) k.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := by
    intro v v' hv
    apply Subtype.ext
    exact ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary v.2.1 v'.2.1
      (fun k hk => congrFun hv ⟨k, hk⟩)
  have hf : Continuous (f : G → ℂ) :=
    ((mem_principalSeries_iff ℂ n (complexPositionCharacter ds) _).mp f.2.1).1.continuous
  have hfK (g : G) : Continuous (fun k : Kc => (f : G → ℂ) (k.val * g)) :=
    hf.comp (continuous_subtype_val.mul continuous_const)
  obtain ⟨m, v, κ', hκ', hv⟩ :=
    exists_compactPairing_expansion μ (unitaryCompact ℂ n).subtype f hfK κ hκ
      (hasFiniteCompactConvolutionKernel_of_finite_translates κ hκ hκfin) ρ hρ p hp
  let W := fun j => B (v j)
  have hp' (x g : G) : (∫ k, κ k * B f (x * k.val * g) ∂μ) =
      ∑ j, W j x * (∫ k, κ' j k * (f : G → ℂ) (k.val * g) ∂μ) := by
    rw [← hProj, hv, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, W]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨m, W, κ', ?_, fun x g => ⟨hp' x g, ?_⟩⟩
  · intro j
    exact ⟨Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v j, rfl⟩), hκ' j⟩
  · let wx := GeneralLinear.weylLong n ℂ * ι x
    have hi (k : Kc) : wd (B f) (x * ι k.val * g) = B f (wx * k.val * ι g) := by
      simp only [ArchimedeanLocal.dualFunction, wx, map_mul,
        GeneralLinear.inverseTranspose_involutive, mul_assoc]
    simp_rw [hi]
    exact hp' wx (ι g)

end ComplexPrincipalSeries

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
