import Langlands.Global.Factors.HeckeMixedComponents
import Langlands.Global.Factors.HeckeDivisorEulerProduct
import Langlands.Global.Hecke.AdelicLattice
import Langlands.Global.Factors.HeckeDivisorClasses

/-! # Finite theta coefficients of actual Hecke characters -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Topology NumberField NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

theorem ord_uniformizerUnit_zpow (k : ℤ) :
    T.ord ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) = k := by
  rw [Units.val_zpow_eq_zpow_val, T.ord_zpow, uniformizerUnit_ord, mul_one]

theorem ord_uniformizerUnit_zpow_inv_mul (x : F.Carrierˣ) :
    T.ord (((uniformizerUnit T ^ T.ord (x : F.Carrier))⁻¹ * x : F.Carrierˣ) : F.Carrier) =
      0 := by
  rw [Units.val_mul, T.ord_mul (Units.ne_zero _) x.ne_zero, Units.val_inv_eq_inv_val,
    T.ord_inv, ord_uniformizerUnit_zpow, neg_add_cancel]

/-- A quasicharacter of multiplicative conductor zero is trivial on units of order zero. -/
theorem character_eq_one_of_conductor_eq_zero (χ : Character)
    (hχ : T.multiplicativeConductor χ = 0) (w : F.Carrierˣ)
    (hw : T.ord (w : F.Carrier) = 0) : χ w = 1 :=
  ((conductorAt_iff T χ 0).mpr hχ.symm).1 w (by simpa [unitLevel] using hw)

/-- For a function with inverse-character covariance under order-zero units, the shell
Mellin coefficient of order `k` is computed at `π ^ k * w` for every unit `w` of order zero. -/
theorem shellMellinTerm_eq_of_covariant (f : F.Carrier → ℂ) (η : Character)
    (hf : ∀ (x : F.Carrier) (w : F.Carrierˣ), T.ord (w : F.Carrier) = 0 →
      f (x * w) = (η w : ℂ)⁻¹ * f x)
    (s : ℂ) (k : ℤ) (w : F.Carrierˣ) (hw : T.ord (w : F.Carrier) = 0) :
    shellMellinTerm T f η s k =
      f ((uniformizerUnit T ^ k * w : F.Carrierˣ) : F.Carrier) *
        (η (uniformizerUnit T ^ k * w) : ℂ) * spectralVariable T s ^ k := by
  have hne : (η w : ℂ) ≠ 0 := (η w).ne_zero
  rw [shellMellinTerm, Units.val_mul, hf _ w hw, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, mul_zpow]
  field_simp
  rw [Units.val_zpow_eq_zpow_val]
  ring

/-- For a function with inverse-character covariance under order-zero units, the shell
Mellin coefficient at the order of a unit is computed at that unit itself. -/
theorem shellMellinTerm_ord_of_covariant (f : F.Carrier → ℂ) (η : Character)
    (hf : ∀ (x : F.Carrier) (w : F.Carrierˣ), T.ord (w : F.Carrier) = 0 →
      f (x * w) = (η w : ℂ)⁻¹ * f x)
    (s : ℂ) (x : F.Carrierˣ) :
    shellMellinTerm T f η s (T.ord (x : F.Carrier)) =
      f x * (η x : ℂ) * spectralVariable T s ^ T.ord (x : F.Carrier) := by
  have h := shellMellinTerm_eq_of_covariant T f η hf s (T.ord (x : F.Carrier)) _
    (ord_uniformizerUnit_zpow_inv_mul T x)
  rw [mul_inv_cancel_left] at h
  exact h

/-- The actual Euler test is evaluated at a unit through its shell Mellin coefficient. -/
theorem shellMellinTerm_eulerTest_ord (χ : Character) (s : ℂ) (x : F.Carrierˣ) :
    shellMellinTerm T (eulerTest T χ) χ s (T.ord (x : F.Carrier)) =
      eulerTest T χ x * (χ x : ℂ) * spectralVariable T s ^ T.ord (x : F.Carrier) :=
  shellMellinTerm_ord_of_covariant T _ χ
    (fun y w hw => eulerTest_mul_integralUnit T χ w hw y) s x

/-- The actual Euler test is bounded by one. -/
theorem norm_eulerTest_le_one (χ : Character) (x : F.Carrier) : ‖eulerTest T χ x‖ ≤ 1 := by
  classical
  rw [show eulerTest T χ x = (eulerTest T χ : F.Carrier → ℂ) x from rfl, eulerTest_coe]
  by_cases hc : T.multiplicativeConductor χ = 0
  · rw [ite_eq_left hc]
    by_cases hx : x ∈ integerRing T
    · rw [Set.indicator_of_mem hx, norm_one]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  · rw [ite_eq_right hc]
    by_cases hx : x ∈ integralUnits T
    · rw [Set.indicator_of_mem hx, norm_inv, norm_characterExtension_on_units T χ hx, inv_one]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one

/-- The actual Euler test is supported on the integer ring. -/
theorem mem_additiveLattice_zero_of_eulerTest_ne_zero (χ : Character) {x : F.Carrier}
    (hx : eulerTest T χ x ≠ 0) : x ∈ T.additiveLattice 0 := by
  classical
  rw [show eulerTest T χ x = (eulerTest T χ : F.Carrier → ℂ) x from rfl, eulerTest_coe] at hx
  by_cases hc : T.multiplicativeConductor χ = 0
  · rw [ite_eq_left hc] at hx
    have h := Set.mem_of_indicator_ne_zero hx
    rw [integerRing_eq_lattice_zero] at h
    exact h
  · rw [ite_eq_right hc] at hx
    have h := Set.mem_of_indicator_ne_zero hx
    rw [T.mem_additiveLattice, (mem_integralUnits_iff_valuation T x).mp h, WithZero.exp_zero]

/-- An unramified Euler test is one on the integer ring. -/
theorem eulerTest_eq_one_of_mem (χ : Character) (hχ : T.multiplicativeConductor χ = 0)
    {x : F.Carrier} (hx : x ∈ T.additiveLattice 0) : eulerTest T χ x = 1 := by
  classical
  rw [show eulerTest T χ x = (eulerTest T χ : F.Carrier → ℂ) x from rfl, eulerTest_coe,
    ite_eq_left hχ, integerRing_eq_lattice_zero, Set.indicator_of_mem (by exact hx)]

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.Global.HeckeTheta

open Langlands.LocalFactor.PadicAbelian Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.Global.HeckeDivisor
open Langlands.Global.HeckeDivisorEulerProduct
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

local instance heckeThetaCoefficientsDecidableEq : DecidableEq (FinitePlace K) := Classical.decEq _

/-- The image of a nonzero global element as a unit of a finite completion. -/
def localUnit (v : FinitePlace K) (a : Kˣ) : (FiniteCompletion K v)ˣ :=
  Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a

@[simp] theorem localUnit_val (v : FinitePlace K) (a : Kˣ) :
    (localUnit v a : FiniteCompletion K v) = algebraMap K (FiniteCompletion K v) a :=
  rfl

/-- Local orders of a global element are the coefficients of its principal divisor. -/
theorem ord_localUnit (v : FinitePlace K) (a : Kˣ) :
    (topologicalData v).ord (localUnit v a : FiniteCompletion K v) = principalDivisor a v := by
  rw [principalDivisor, ideleDivisor_apply_eq_ord]
  rfl

/-- Every actual Hecke character has multiplicative conductor zero outside a finite set. -/
theorem exists_finset_conductor_eq_zero (χ : HeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S,
      (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0 := by
  obtain ⟨S, hS⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt K χ
  exact ⟨S, fun v hv =>
    HeckeFunctionalEquation.multiplicativeConductor_eq_zero_of_isUnramifiedAt χ v (hS v hv)⟩

/-- The local components are one on a global element away from a finite set containing the
support of its principal divisor. -/
theorem exists_finset_finiteComponent_localUnit_eq_one (χ : HeckeCharacter K) (a : Kˣ) :
    ∃ S : Finset (FinitePlace K), (principalDivisor a).support ⊆ S ∧
      ∀ v ∉ S, χ.finiteComponent v (localUnit v a) = 1 := by
  obtain ⟨R, hR⟩ := exists_finset_conductor_eq_zero χ
  refine ⟨R ∪ (principalDivisor a).support, Finset.subset_union_right, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not] at hv
  exact character_eq_one_of_conductor_eq_zero _ _ (hR v hv.1) _
    ((ord_localUnit v a).trans hv.2)

section Mixed

variable (χ : HeckeCharacter K)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))

include hR hC

/-- The finite part of the product formula on a principal idele, as an unordered product,
in the supplied mixed-coordinate presentation of the infinite character. -/
theorem finprod_finiteComponent_localUnit (a : Kˣ) :
    ∏ᶠ v : FinitePlace K, (χ.finiteComponent v (localUnit v a) : ℂ) =
      (Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent) (mixedEmbedding K (a : K)))⁻¹ := by
  obtain ⟨R, -, hR1⟩ := exists_finset_finiteComponent_localUnit_eq_one χ a
  let S : Finset (FinitePlace K) := HeckeFunctionalEquation.multiplicativeIntegralControl χ ∪
    HeckeFunctionalEquation.nonunitPlaces (diagonalUnits K a) ∪ R
  have h := HeckeFunctionalEquation.character_eq_mixed_mul_finite χ dR hR dC hC
    (diagonalUnits K a) S (Finset.subset_union_left.trans Finset.subset_union_left)
    (Finset.subset_union_right.trans Finset.subset_union_left)
  rw [HeckeCharacter.onIdeles_diagonalUnits, Units.val_one,
    HeckeFunctionalEquation.mixedInfiniteUnit_diagonal] at h
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra hvS
    exact hv (by
      dsimp only
      rw [hR1 v (fun h => hvS (Finset.mem_union_right _ h)), Units.val_one]))]
  exact eq_inv_of_mul_eq_one_right h.symm

end Mixed

/-- The complex power of the mixed norm of a nonzero global element is the product of the
actual local spectral variables at its principal divisor. -/
theorem mixedNorm_cpow_eq_prod (a : Kˣ) (s : ℂ) (S : Finset (FinitePlace K))
    (hS : (principalDivisor a).support ⊆ S) :
    ((mixedEmbedding.norm (mixedEmbedding K (a : K)) : ℝ) : ℂ) ^ (-s) =
      ∏ v ∈ S, spectralVariable (topologicalData v) s ^ principalDivisor a v := by
  have hN : mixedEmbedding.norm (mixedEmbedding K (a : K)) =
      ∏ v ∈ (principalDivisor a).support,
        (Ideal.absNorm v.asIdeal : ℝ) ^ principalDivisor a v := by
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, ← HeckeDivisor.norm_principalDivisor]
    rfl
  have hpos : ∀ v ∈ (principalDivisor a).support,
      (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ principalDivisor a v := fun v _ =>
    zpow_pos (lt_trans zero_lt_one (by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)) _
  have hprod := Finset.prod_pos hpos
  rw [← Finset.prod_subset hS (fun v _ hv => by
      rw [Finsupp.notMem_support_iff.mp hv, zpow_zero]),
    hN, Complex.cpow_def_of_ne_zero (by exact_mod_cast hprod.ne'),
    ← Complex.ofReal_log hprod.le, Real.log_prod (fun v hv => (hpos v hv).ne'),
    Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro v _
  rw [spectralVariable_zpow, HeckeEulerProduct.residueCardinality_eq, Real.log_zpow]
  push_cast
  congr 1
  ring

/-- The actual finite Euler-test factor of the theta coefficient at a divisor `d`. -/
def thetaFactor (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (γ : K)
    (v : FinitePlace K) : ℂ :=
  eulerTest (topologicalData v) (χ.finiteComponent v)
    (algebraMap K (FiniteCompletion K v) γ *
      ((uniformizerUnit (topologicalData v) ^ d v : (FiniteCompletion K v)ˣ) :
        FiniteCompletion K v))

/-- The finite theta coefficient: the unordered product of the actual local Euler tests at
`γ π_v ^ d(v)`. -/
def thetaCoeff (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (γ : K) : ℂ :=
  ∏ᶠ v : FinitePlace K, thetaFactor χ d γ v

/-- The ideal-class factor of a finite divisor. -/
def classFactor (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (s : ℂ) : ℂ :=
  ∏ v ∈ d.support, ((χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ) *
    spectralVariable (topologicalData v) s) ^ d v

/-- The theta factors are one outside an explicit finite set. -/
theorem exists_finset_thetaFactor_eq_one (χ : HeckeCharacter K) (d : FinitePlaceDivisor K)
    (γ : K) : ∃ S : Finset (FinitePlace K), ∀ v ∉ S, thetaFactor χ d γ v = 1 := by
  obtain ⟨R, hR⟩ := exists_finset_conductor_eq_zero χ
  let N := (Hecke.finite_setOf_not_mem_additiveLattice_zero γ).toFinset
  refine ⟨R ∪ d.support ∪ N, fun v hv => ?_⟩
  simp only [N, Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
  obtain ⟨⟨hvR, hvd⟩, hvN⟩ := hv
  rw [thetaFactor, hvd, zpow_zero, Units.val_one, mul_one]
  exact eulerTest_eq_one_of_mem _ _ (hR v hvR) hvN

theorem mulSupport_thetaFactor_finite (χ : HeckeCharacter K) (d : FinitePlaceDivisor K)
    (γ : K) : (Function.mulSupport (thetaFactor χ d γ)).Finite := by
  obtain ⟨S, hS⟩ := exists_finset_thetaFactor_eq_one χ d γ
  exact S.finite_toSet.subset fun v hv => by
    by_contra h
    exact hv (hS v h)

/-- The theta coefficient is the finite product over any set outside which its factors are one. -/
theorem thetaCoeff_eq_prod (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (γ : K)
    (S : Finset (FinitePlace K)) (hS : ∀ v ∉ S, thetaFactor χ d γ v = 1) :
    thetaCoeff χ d γ = ∏ v ∈ S, thetaFactor χ d γ v :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
    by_contra h
    exact hv (hS v h)

/-- Nonzero theta coefficients are supported on the lattice ideal of `d`. -/
theorem mem_latticeIdeal_of_thetaCoeff_ne_zero (χ : HeckeCharacter K)
    (d : FinitePlaceDivisor K) (γ : K) (h : thetaCoeff χ d γ ≠ 0) :
    γ ∈ (Hecke.latticeIdeal d : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨S, hS⟩ := exists_finset_thetaFactor_eq_one χ d γ
  rw [thetaCoeff_eq_prod χ d γ S hS] at h
  rw [Hecke.mem_latticeIdeal_iff_forall_mem]
  intro v
  have hv : thetaFactor χ d γ v ≠ 0 := by
    by_cases hvS : v ∈ S
    · exact Finset.prod_ne_zero_iff.mp h v hvS
    · rw [hS v hvS]
      exact one_ne_zero
  have hmem := mem_additiveLattice_zero_of_eulerTest_ne_zero _ _ hv
  have hπ : ((uniformizerUnit (topologicalData v) ^ (-d v) : (FiniteCompletion K v)ˣ) :
      FiniteCompletion K v) ∈ (topologicalData v).additiveLattice (d v) :=
    (uniformizer_pow_mem_additiveLattice _ (d v) (-d v)).mpr le_rfl
  have hprod := Hecke.mul_mem_additiveLattice v hmem hπ
  rw [zero_add, mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
    Units.val_one, mul_one] at hprod
  exact hprod

/-- The theta coefficients are bounded by one. -/
theorem norm_thetaCoeff_le_one (χ : HeckeCharacter K) (d : FinitePlaceDivisor K) (γ : K) :
    ‖thetaCoeff χ d γ‖ ≤ 1 := by
  obtain ⟨S, hS⟩ := exists_finset_thetaFactor_eq_one χ d γ
  rw [thetaCoeff_eq_prod χ d γ S hS, norm_prod]
  exact Finset.prod_le_one₀ (fun v _ => norm_nonneg _)
    (fun v _ => norm_eulerTest_le_one _ _ _)

/-- A global integral unit changes each theta factor by its inverse local character value. -/
theorem thetaFactor_unit_mul (χ : HeckeCharacter K) (d : FinitePlaceDivisor K)
    (u : (𝓞 K)ˣ) (γ : K) (v : FinitePlace K) :
    thetaFactor χ d ((u : 𝓞 K) * γ) v =
      (χ.finiteComponent v (localUnit v (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u)) :
        ℂ)⁻¹ * thetaFactor χ d γ v := by
  have hw : (topologicalData v).ord ((localUnit v
      (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u) : (FiniteCompletion K v)ˣ) :
        FiniteCompletion K v) = 0 := by
    rw [ord_localUnit, principalDivisor_units_map, Finsupp.coe_zero, Pi.zero_apply]
  rw [thetaFactor, thetaFactor, show algebraMap K (FiniteCompletion K v) ((u : 𝓞 K) * γ) *
      ((uniformizerUnit (topologicalData v) ^ d v : (FiniteCompletion K v)ˣ) :
        FiniteCompletion K v) =
      (algebraMap K (FiniteCompletion K v) γ *
        ((uniformizerUnit (topologicalData v) ^ d v : (FiniteCompletion K v)ˣ) :
          FiniteCompletion K v)) *
        ((localUnit v (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u) :
          (FiniteCompletion K v)ˣ) : FiniteCompletion K v) by
      rw [localUnit_val, map_mul]
      simp only [Units.coe_map, MonoidHom.coe_coe]
      ring]
  exact eulerTest_mul_integralUnit _ _ _ hw _

section Mixed

variable (χ : HeckeCharacter K)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))

include hR hC

/-- Unit equivariance of the theta coefficients. -/
theorem thetaCoeff_unit_mul (d : FinitePlaceDivisor K) (u : (𝓞 K)ˣ) (γ : K) :
    thetaCoeff χ d ((u : 𝓞 K) * γ) =
      Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent)
        (mixedEmbedding K ((u : 𝓞 K) : K)) * thetaCoeff χ d γ := by
  let a : Kˣ := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u
  obtain ⟨Sθ, hSθ⟩ := exists_finset_thetaFactor_eq_one χ d γ
  obtain ⟨Sχ, -, hSχ⟩ := exists_finset_finiteComponent_localUnit_eq_one χ a
  let S : Finset (FinitePlace K) := Sθ ∪ Sχ
  have hθ : ∀ v ∉ S, thetaFactor χ d γ v = 1 := fun v hv =>
    hSθ v (fun h => hv (Finset.mem_union_left _ h))
  have hχ1 : ∀ v ∉ S, χ.finiteComponent v (localUnit v a) = 1 := fun v hv =>
    hSχ v (fun h => hv (Finset.mem_union_right _ h))
  have hθu : ∀ v ∉ S, thetaFactor χ d ((u : 𝓞 K) * γ) v = 1 := fun v hv => by
    rw [thetaFactor_unit_mul, hθ v hv, hχ1 v hv, Units.val_one, inv_one, mul_one]
  have hprod := finprod_finiteComponent_localUnit χ dR hR dC hC a
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra hvS
    exact hv (by dsimp only; rw [hχ1 v hvS, Units.val_one]))] at hprod
  rw [thetaCoeff_eq_prod χ d _ S hθu, thetaCoeff_eq_prod χ d γ S hθ]
  simp only [thetaFactor_unit_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hprod, inv_inv]
  rfl

/-- The finite theta coefficient, divided by the mixed character and multiplied by the
complex norm power and class factor, is exactly the actual divisor Euler coefficient. -/
theorem thetaCoeff_mul_eq_coefficient (d : FinitePlaceDivisor K) (γ : Kˣ) (s : ℂ) :
    thetaCoeff χ d γ *
        (Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
          (fun v => (dC v).weight) (fun v => (dC v).exponent)
          (mixedEmbedding K (γ : K)))⁻¹ *
        ((mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℝ) : ℂ) ^ (-s) *
        classFactor χ d s =
      DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s)
        (principalDivisor γ + d) := by
  obtain ⟨Sθ, hSθ⟩ := exists_finset_thetaFactor_eq_one χ d γ
  obtain ⟨Sχ, hpd, hSχ⟩ := exists_finset_finiteComponent_localUnit_eq_one χ γ
  let S : Finset (FinitePlace K) := Sθ ∪ Sχ ∪ d.support
  have hθS : Sθ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hχS : Sχ ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hdS : d.support ⊆ S := Finset.subset_union_right
  have hθ : ∀ v ∉ S, thetaFactor χ d γ v = 1 := fun v hv => hSθ v (fun h => hv (hθS h))
  have hprod := finprod_finiteComponent_localUnit χ dR hR dC hC γ
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra hvS
    exact hv (by dsimp only; rw [hSχ v (fun h => hvS (hχS h)), Units.val_one]))] at hprod
  have he : (principalDivisor γ + d).support ⊆ S := Finsupp.support_add.trans
    (Finset.union_subset (hpd.trans hχS) hdS)
  rw [thetaCoeff_eq_prod χ d γ S hθ, ← hprod, mixedNorm_cpow_eq_prod γ s S (hpd.trans hχS),
    classFactor, Finset.prod_subset hdS (fun v _ hv => by
      rw [Finsupp.notMem_support_iff.mp hv, zpow_zero]),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    DivisorEulerProduct.coefficient, Finset.empty_union,
    Finset.prod_subset he (fun v _ hv => by
      rw [Finsupp.notMem_support_iff.mp hv, shellWeight_zero])]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hx : (topologicalData v).ord ((localUnit v γ * uniformizerUnit (topologicalData v) ^ d v :
      (FiniteCompletion K v)ˣ) : FiniteCompletion K v) = (principalDivisor γ + d) v := by
    rw [Units.val_mul, (topologicalData v).ord_mul (Units.ne_zero _) (Units.ne_zero _),
      ord_localUnit, ord_uniformizerUnit_zpow, Finsupp.add_apply]
  have hloc := shellMellinTerm_eulerTest_ord (topologicalData v) (χ.finiteComponent v) s
    (localUnit v γ * uniformizerUnit (topologicalData v) ^ d v)
  rw [hx] at hloc
  rw [shellWeight, hloc, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Finsupp.add_apply, zpow_add₀ (spectralVariable_ne_zero _ s), mul_zpow, thetaFactor,
    Units.val_mul, localUnit_val]
  simp only [Units.val_zpow_eq_zpow_val]
  ring

end Mixed

end Langlands.Global.HeckeTheta
