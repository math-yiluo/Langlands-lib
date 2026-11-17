import Langlands.Representation.Archimedean.GKModuleOrthogonal
import Langlands.Representation.Archimedean.ComplexPermutationKType
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexSwapJacquetLie
import Langlands.Representation.Archimedean.ComplexJacquetReduction
import Langlands.Representation.Archimedean.ComplexTemperedIrreducibleStatement
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexDuality.GramWeight
import Langlands.Representation.Archimedean.ComplexJacquetKernel
import Langlands.Representation.Archimedean.ComplexJacquetLimit

/-!
# Complements of submodules of tempered complex standard modules

Let `ds` be a list of `n` complex characters whose exponents all have the same real part `r`,
and let `X(ds)` be the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite functions of the standard module
of `ds`, with the `U(n)`-invariant positive definite form `B(f, h) = ∫_{U(n)} f conj(h)`
(`ComplexPermutation.unitaryForm`).

* `ComplexTemperedComplement.unitaryForm_lie_add`: `B(R(X) f, h) + B(f, R(X) h)` is a fixed
  multiple of `B(f, h)`; the factor is `-c_X`, minus the derivative `c_X` at `1` of
  `|det|^(-4r)` along `X`, and is zero for unitary characters (`r = 0`).
* `ComplexTemperedComplement.sup_orth_eq_top`: in any representation of a group with finite
  vectors, a vector functional separating orbits and an invariant positive definite form, every
  invariant subspace `U` satisfies `U + U^⊥ = V`.

Together they prove `ComplexTemperedComplementStatement`: every `(𝔤, K)`-submodule of `X(ds)` has
the `(𝔤, K)`-stable complement `W^⊥`. Consequently the irreducibility statement
`ComplexTemperedStandardIrreducibleStatement` follows from each of

* `ComplexTemperedEndScalarStatement` (every `(𝔤, K)`-endomorphism of `X(ds)` is a scalar),
* `ComplexTemperedCommonVectorStatement` (a nonzero vector lies in every nonzero
  `(𝔤, K)`-submodule),
* `ComplexTemperedJacquetUniqueStatement` (every Jacquet functional with the exponents of
  evaluation at `1` is a multiple of evaluation at `1`), which implies the first.

Separately, `complexTemperedCyclicVector` proves the conditional criterion
`ComplexTemperedCyclicVectorStatement`: a module with a nonzero cyclic vector that every
`U(n)`-equivariant endomorphism maps to a multiple of itself is irreducible. Using it to prove
`ComplexTemperedStandardIrreducibleStatement` still requires constructing, for each tempered
list, a vector with these properties; this module constructs none.
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Matrix ComplexConjugate TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexTemperedComplement

/-! ## Orthogonal complements for an invariant positive definite form -/



/-! ## Calculus on `GL_n(ℂ)` -/

section Calculus

open Langlands.GeneralLinear ComplexMaximalParabolicIntegration

variable {n : ℕ}

/-- The weight `g ↦ (|det g|²)^c`. -/
def detWeight (c : ℝ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  ((Complex.normSq ((g : Matrix (Fin n) (Fin n) ℂ).det) ^ c : ℝ) : ℂ)

theorem detWeight_mul (c : ℝ) (g h : Langlands.GeneralLinear n ℂ) :
    detWeight c (g * h) = detWeight c g * detWeight c h := by
  simp only [detWeight, Units.val_mul, Matrix.det_mul, map_mul]
  rw [Real.mul_rpow (Complex.normSq_nonneg _) (Complex.normSq_nonneg _), Complex.ofReal_mul]

theorem detWeight_unitary (c : ℝ) {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) : detWeight c k = 1 := by
  have h := normSqC_det_unitary (⟨k, hk⟩ : unitaryCompact ℂ n)
  unfold normSqC at h
  have h' : Complex.normSq ((k : Matrix (Fin n) (Fin n) ℂ).det) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact_mod_cast h
  simp only [detWeight, h', Real.one_rpow, Complex.ofReal_one]

theorem detWeight_borel (c : ℝ) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    detWeight c ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g) =
      ((∏ i : Fin n, Complex.normSq (a i : ℂ) ^ c : ℝ) : ℂ) * detWeight c g := by
  rw [detWeight_mul, detWeight_mul]
  have hu : detWeight c (u : Langlands.GeneralLinear n ℂ) = 1 := by
    simp [detWeight, det_upperUnipotent]
  rw [hu, mul_one]
  congr 1
  simp only [detWeight, Iwasawa.diagonalUnits_val, Matrix.det_diagonal, map_prod]
  rw [Real.finsetProd_rpow _ _ (fun i _ => Complex.normSq_nonneg _)]

theorem contMDiff_detWeight (c : ℝ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (detWeight (n := n) c) := by
  refine contMDiff_of_contDiffOn (ψ := fun Y : Matrix (Fin n) (Fin n) ℂ =>
    ((Complex.normSq Y.det ^ c : ℝ) : ℂ)) ?_ fun g => rfl
  intro Y hY
  have hY' : IsUnit Y := hY
  have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY').ne_zero
  have hn : ContDiff ℝ ∞ fun Y : Matrix (Fin n) (Fin n) ℂ => Complex.normSq Y.det := by
    have : (fun Y : Matrix (Fin n) (Fin n) ℂ => Complex.normSq Y.det) =
        fun Y => ‖Y.det‖ ^ 2 := funext fun Y => Complex.normSq_eq_norm_sq _
    rw [this]
    exact (contDiff_norm_sq ℝ).comp contDiff_det
  have hne : Complex.normSq Y.det ≠ 0 := (Complex.normSq_pos.mpr hdet).ne'
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp Y
    (hn.contDiffAt.rpow_const_of_ne (p := c) hne)).contDiffWithinAt

theorem unitsExtension_mul_fun (A C : Langlands.GeneralLinear n ℂ → ℂ) :
    unitsExtension (fun g => A g * C g) = fun y => unitsExtension A y * unitsExtension C y := by
  funext y
  unfold unitsExtension
  split_ifs <;> simp

theorem unitsExtension_conj (A : Langlands.GeneralLinear n ℂ → ℂ) :
    unitsExtension (fun g => conj (A g)) = fun y => conj (unitsExtension A y) := by
  funext y
  unfold unitsExtension
  split_ifs <;> simp

/-- The product rule for right derivatives on `GL_n(ℂ)`. -/
theorem rightDerivative_mul_fun {A C : Langlands.GeneralLinear n ℂ → ℂ}
    (hA : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ A) (hC : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ C)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (fun g => A g * C g) g =
      rightDerivative (matrixModel ℂ n) X A g * C g +
        A g * rightDerivative (matrixModel ℂ n) X C g := by
  rw [rightDerivative_eq_fderiv (ComplexJacquetLimit.contMDiff_mul_fun hA hC),
    rightDerivative_eq_fderiv hA, rightDerivative_eq_fderiv hC, unitsExtension_mul_fun]
  have hg : IsUnit (g : Matrix (Fin n) (Fin n) ℂ) := Units.isUnit g
  rw [fderiv_fun_mul (differentiableAt_unitsExtension hA hg) (differentiableAt_unitsExtension hC hg)]
  simp only [add_apply, smul_apply, smul_eq_mul,
    unitsExtension_val]
  ring

theorem contMDiff_conj {A : Langlands.GeneralLinear n ℂ → ℂ}
    (hA : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ A) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (fun g => conj (A g)) := by
  refine contMDiff_of_contDiffOn (ψ := fun y => Complex.conjCLE (unitsExtension A y))
    (Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_unitsExtension hA)) fun g => ?_
  rw [unitsExtension_val, Complex.conjCLE_apply]

/-- Right derivatives commute with complex conjugation (they are real derivatives). -/
theorem rightDerivative_conj {A : Langlands.GeneralLinear n ℂ → ℂ}
    (hA : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ A)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (fun g => conj (A g)) g =
      conj (rightDerivative (matrixModel ℂ n) X A g) := by
  rw [rightDerivative_eq_fderiv (contMDiff_conj hA), rightDerivative_eq_fderiv hA,
    unitsExtension_conj]
  change fderiv ℝ (fun y => star (unitsExtension A y)) _ _ = star _
  rw [fderiv_star]
  rfl

/-- `R(X)` of the weight at `k` is the weight at `k` times `R(X)` of the weight at `1`. -/
theorem rightDerivative_detWeight (c : ℝ) (X : Matrix (Fin n) (Fin n) ℂ)
    (k : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (detWeight (n := n) c) k =
      detWeight c k *
        rightDerivative (matrixModel ℂ n) X (detWeight (n := n) c) (1 : Langlands.GeneralLinear n ℂ) := by
  have h := rightDerivative_mul_left_of_eq (F := ℂ) (N := n) (contMDiff_detWeight (n := n) c) (a := k) (c := detWeight c k)
    (fun g => detWeight_mul c k g) X 1
  rwa [mul_one] at h

end Calculus

/-! ## The tempered standard module -/

section Concrete

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexPermutation
  ComplexPartialJacquet ComplexGramFormula
open scoped ComplexDuality

variable {n : ℕ}

theorem exists_mem_exponent : ∀ (ds : List ComplexCharacterData) (l : ℕ), l < ds.length →
    ∃ d ∈ ds, complexPositionExponent ds l = d.exponent
  | [], l, hl => by simp at hl
  | d :: _, 0, _ => ⟨d, List.mem_cons_self .., rfl⟩
  | _ :: ds, l + 1, hl => by
      obtain ⟨d, hd, he⟩ := exists_mem_exponent ds l (by simp at hl; omega)
      exact ⟨d, List.mem_cons_of_mem _ hd, he⟩

/-- All exponents of a list whose exponents have equal real parts have the real part of the
first one. -/
theorem re_exponent {ds : List ComplexCharacterData} (hlen : ds.length = n)
    (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) {l : ℕ} (hl : l < n) :
    (complexPositionExponent ds l).re = (complexPositionExponent ds 0).re := by
  obtain ⟨d, hd, he⟩ := exists_mem_exponent ds l (by omega)
  obtain ⟨d₀, hd₀, he₀⟩ := exists_mem_exponent ds 0 (by omega)
  rw [he, he₀]
  exact htemp d hd d₀ hd₀

/-- The dual partner `g ↦ |det g|^(-4r) conj (h g)` of `h`. -/
def dualPartner (r : ℝ) (h : Langlands.GeneralLinear n ℂ → ℂ)
    (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  detWeight (-(2 * r)) g * conj (h g)

/-- If the exponents of `ds` all have real part `r`, the dual partner of a function of the
standard module of `ds` lies in the principal series of the inverse characters. -/
theorem dualPartner_mem {ds : List ComplexCharacterData} (hlen : ds.length = n)
    (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ complexStandardModule n ds) :
    dualPartner (complexPositionExponent ds 0).re h ∈
      principalSeries ℂ n (dualChar (complexPositionCharacter ds)) := by
  have hχ := ComplexStrictLanglandsQuotient.isPhasePower ds
  refine ⟨ComplexJacquetLimit.contMDiff_mul_fun (contMDiff_detWeight _) (contMDiff_conj hh.1),
    fun a u g => ?_⟩
  have key := ComplexDuality.normSq_mul_star_principalSeriesCharacter (n := n)
    (χ := dualChar (complexPositionCharacter ds)) (χ' := complexPositionCharacter ds)
    (fun i z => inv_mul_cancel₀ (hχ.ne_zero i z))
    (s := fun i => -(2 * (complexPositionExponent ds i).re))
    (fun i z => ComplexJacquetKernel.normSq_dualChar hχ i z) a
  have hprod : (∏ i : Fin n,
      Complex.normSq (a i : ℂ) ^ (-(2 * (complexPositionExponent ds 0).re))) =
      ∏ i : Fin n, Complex.normSq (a i : ℂ) ^ (-(2 * (complexPositionExponent ds i).re)) :=
    Finset.prod_congr rfl fun i _ => by rw [re_exponent hlen htemp i.isLt]
  change detWeight _ (_ * _ * g) * conj (h (_ * _ * g)) = _ * (detWeight _ g * conj (h g))
  rw [hh.2 a u g, detWeight_borel, map_mul, ← key, hprod, Complex.star_def]
  ring

/-- **Skewness of the invariant form up to a scalar.** If the exponents of `ds` all have real
part `r`, then `B(R(X) f, h) + B(f, R(X) h) = -c_X B(f, h)`, where `c_X` is the derivative at `1`
of `|det|^(-4r)` along `X`. This is the infinitesimal invariance of the pairing between the
standard module of `ds` and the principal series of the inverse characters, applied to `f` and
the dual partner of `h`. -/
theorem unitaryForm_lie_add {ds : List ComplexCharacterData} (hlen : ds.length = n)
    (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    (X : Matrix (Fin n) (Fin n) ℂ) (f h : KF n ds) :
    unitaryForm n ds (complexStandardLie n ds (1 ⊗ₜ X) f) h +
        unitaryForm n ds f (complexStandardLie n ds (1 ⊗ₜ X) h) =
      -(rightDerivative (matrixModel ℂ n) X
          (detWeight (n := n) (-(2 * (complexPositionExponent ds 0).re)))
          (1 : Langlands.GeneralLinear n ℂ)) * unitaryForm n ds f h := by
  have hχ : ∀ i z, complexPositionCharacter ds i z *
      dualChar (complexPositionCharacter ds) i z = 1 :=
    fun i z => mul_inv_cancel₀ ((ComplexStrictLanglandsQuotient.isPhasePower ds).ne_zero i z)
  have hP := dualPartner_mem hlen htemp h.2.1
  have hzero := ComplexDuality.integral_rightDerivative_mul_add_eq_zero (ComplexDuality.unitaryHaar n) _ _ hχ
    f.2.1 hP X
  set r := (complexPositionExponent ds 0).re
  set c := rightDerivative (matrixModel ℂ n) X (detWeight (n := n) (-(2 * r)))
    (1 : Langlands.GeneralLinear n ℂ)
  have hhs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (h : Langlands.GeneralLinear n ℂ → ℂ) :=
    h.2.1.1
  have hPk : ∀ k : unitaryCompact ℂ n,
      dualPartner r h (k : Langlands.GeneralLinear n ℂ) =
        conj ((h : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ)) := fun k => by
    rw [dualPartner, detWeight_unitary _ k.2, one_mul]
  have hRPk : ∀ k : unitaryCompact ℂ n,
      rightDerivative (matrixModel ℂ n) X (dualPartner r h) (k : Langlands.GeneralLinear n ℂ) =
        c * conj ((h : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ)) +
          conj (rightDerivative (matrixModel ℂ n) X (h : Langlands.GeneralLinear n ℂ → ℂ)
            (k : Langlands.GeneralLinear n ℂ)) := fun k => by
    rw [show dualPartner r h = fun g => detWeight (-(2 * r)) g *
        conj ((h : Langlands.GeneralLinear n ℂ → ℂ) g) from rfl,
      rightDerivative_mul_fun (contMDiff_detWeight _) (contMDiff_conj hhs),
      rightDerivative_conj hhs, rightDerivative_detWeight, detWeight_unitary _ k.2]
    ring
  simp only [hPk, hRPk] at hzero
  set Rf := complexStandardLie n ds (1 ⊗ₜ X) f
  set Rh := complexStandardLie n ds (1 ⊗ₜ X) h
  have hRf : ((Rf : KF n ds) : Langlands.GeneralLinear n ℂ → ℂ) =
      rightDerivative (matrixModel ℂ n) X f :=
    principalSeriesLie_one_tmul_apply_coe ℂ n _ X f
  have hRh : ((Rh : KF n ds) : Langlands.GeneralLinear n ℂ → ℂ) =
      rightDerivative (matrixModel ℂ n) X h :=
    principalSeriesLie_one_tmul_apply_coe ℂ n _ X h
  rw [← hRf, ← hRh] at hzero
  have e1 : (fun k : unitaryCompact ℂ n =>
      (f : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ) *
        (c * conj ((h : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ)) +
          conj ((Rh : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ)))) =
      fun k : unitaryCompact ℂ n =>
        c * ((f : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ) *
          conj ((h : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ))) +
        (f : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ) *
          conj ((Rh : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ)) :=
    funext fun k => by ring
  rw [e1, integral_add ((integrable_mul_conj ds f h).const_mul c) (integrable_mul_conj ds f Rh),
    integral_const_mul] at hzero
  rw [unitaryForm_apply, unitaryForm_apply, unitaryForm_apply]
  linear_combination hzero

/-- The orthogonal of a subspace stable under the Lie algebra action is stable. -/
theorem orth_lie_mem {ds : List ComplexCharacterData} (hlen : ds.length = n)
    (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) (W : Submodule ℂ (KF n ds))
    (hW : ∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W)
    (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) {x : KF n ds} (hx : x ∈ orth (unitaryForm n ds) W) :
    complexStandardLie n ds Z x ∈ orth (unitaryForm n ds) W := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
      have h1 : complexStandardLie n ds (z ⊗ₜ X) = z • complexStandardLie n ds (1 ⊗ₜ X) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, LinearMap.smul_apply]
      refine Submodule.smul_mem _ z fun y hy => ?_
      have := unitaryForm_lie_add hlen htemp X x y
      rw [hx y hy, mul_zero, hx _ (hW _ y hy), add_zero] at this
      exact this
  | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂

/-- Evaluation at `1` composed with a `𝔤`-equivariant endomorphism is a Jacquet functional
with the exponents `κ_j(1)`, `κ_j(i)` of the standard module. -/
theorem isComplexJacquetFunctional_eval_comp {ds : List ComplexCharacterData}
    (hn : ds.length = n) (E : KF n ds →ₗ[ℂ] KF n ds)
    (hEL : ∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (f : KF n ds),
      E (complexStandardLie n ds Z f) = complexStandardLie n ds Z (E f)) :
    IsComplexJacquetFunctional n (complexStandardLie n ds)
      (kFiniteEval (complexStandardModule n ds) 1 ∘ₗ E)
      (fun j => ComplexSwapJacquet.kappa ds hn j 1)
      (fun j => ComplexSwapJacquet.kappa ds hn j Complex.I) := by
  refine ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
  · rw [LinearMap.comp_apply, hEL, kFiniteEval_apply, principalSeriesLie_one_tmul_apply_coe]
    exact ComplexSwapJacquet.rightDerivative_one_strictUpper (E v).2.1 X fun a b h => hX a b h
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hEL, kFiniteEval_apply, kFiniteEval_apply,
      principalSeriesLie_one_tmul_apply_coe]
    exact ComplexSwapJacquet.rightDerivative_one_diag hn (E v).2.1 j 1
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hEL, kFiniteEval_apply, kFiniteEval_apply,
      principalSeriesLie_one_tmul_apply_coe]
    exact ComplexSwapJacquet.rightDerivative_one_diag hn (E v).2.1 j Complex.I

end Concrete

end ComplexTemperedComplement

open ComplexTemperedComplement ComplexPermutation Langlands.LocalFactor.Archimedean

/-- **Complements in tempered standard modules.** Let `ds` be a list of `n` complex characters
whose exponents all have the same real part. Every `(𝔤𝔩_n(ℂ), U(n))`-submodule `W` of the
`U(n)`-finite functions of `complexStandardModule n ds` has a `(𝔤𝔩_n(ℂ), U(n))`-stable
complement `W'`. -/
def ComplexTemperedComplementStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
    ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
      ∃ W' : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W', complexStandardRep n ds k w ∈ W') ∧
        (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W', complexStandardLie n ds Z w ∈ W') ∧
        IsCompl W W'

/-- The complement is the orthogonal `W^⊥` for the `U(n)`-invariant form
`B(f, h) = ∫_{U(n)} f conj(h)`. -/
theorem complexTemperedComplement : ComplexTemperedComplementStatement := by
  intro n ds hlen htemp W hWK hWL
  exact ⟨orth (unitaryForm n ds) W,
    orth_invariant (unitaryForm n ds) (unitaryForm_invariant ds) W hWK,
    fun Z x hx => orth_lie_mem hlen htemp W hWL Z hx,
    isCompl_orth (unitaryForm n ds) (unitaryForm_self_eq_zero ds)
      (kFiniteEval (complexStandardModule n ds) 1) (kFiniteEval_one_separating ds)
      (isFiniteVector_complexStandardRep ds) (unitaryForm_invariant ds) W hWK⟩

/-- **Schur's lemma for tempered standard modules.** For a list `ds` of `n` complex characters
whose exponents all have the same real part, every `(𝔤𝔩_n(ℂ), U(n))`-endomorphism of the
`U(n)`-finite functions of `complexStandardModule n ds` is a scalar. -/
def ComplexTemperedEndScalarStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
    ∀ E : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
        E (complexStandardRep n ds k f) = complexStandardRep n ds k (E f)) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) f,
        E (complexStandardLie n ds Z f) = complexStandardLie n ds Z (E f)) →
      ∃ c : ℂ, ∀ f, E f = c • f

/-- Scalar endomorphisms give irreducibility: the projection onto a `(𝔤, K)`-submodule along a
`(𝔤, K)`-stable complement is a `(𝔤, K)`-endomorphism, hence `0` or the identity. -/
theorem complexTemperedIrreducible_of_endScalar (hE : ComplexTemperedEndScalarStatement) :
    ComplexTemperedStandardIrreducibleStatement := by
  intro n ds hlen htemp
  refine ⟨complexStandardNontrivial n ds hlen, fun W hWK hWL => ?_⟩
  obtain ⟨W', hW'K, hW'L, hc⟩ := complexTemperedComplement n ds hlen htemp W hWK hWL
  obtain ⟨c, hcP⟩ := hE n ds hlen htemp (W.projection W' hc)
    (fun k f => projection_comm hc _ (hWK k) (hW'K k) f)
    (fun Z f => projection_comm hc _ (hWL Z) (hW'L Z) f)
  by_cases h0 : c = 0
  · left
    have htop : W' = ⊤ := eq_top_iff.mpr fun f _ => by
      rw [← Submodule.projection_apply_eq_zero_iff hc, hcP, h0, zero_smul]
    have := hc.inf_eq_bot
    rwa [htop, inf_top_eq] at this
  · right
    refine eq_top_iff.mpr fun f _ => ?_
    have h1 : f = c⁻¹ • W.projection W' hc f := by
      rw [hcP, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [h1]
    exact W.smul_mem _ (Submodule.projection_apply_mem hc f)

/-- **A common vector of all nonzero submodules.** For a list `ds` of `n` complex characters
whose exponents all have the same real part, some nonzero vector of the `U(n)`-finite functions
of `complexStandardModule n ds` lies in every nonzero `(𝔤𝔩_n(ℂ), U(n))`-submodule. -/
def ComplexTemperedCommonVectorStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
    ∃ f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n), f₀ ≠ 0 ∧
      ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
        (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
        W ≠ ⊥ → f₀ ∈ W

/-- A common vector gives irreducibility: it cannot lie in both `W` and its complement. -/
theorem complexTemperedIrreducible_of_commonVector (hC : ComplexTemperedCommonVectorStatement) :
    ComplexTemperedStandardIrreducibleStatement := by
  intro n ds hlen htemp
  obtain ⟨f₀, hf₀, hmem⟩ := hC n ds hlen htemp
  refine ⟨nontrivial_of_ne f₀ 0 hf₀, fun W hWK hWL => ?_⟩
  obtain ⟨W', hW'K, hW'L, hc⟩ := complexTemperedComplement n ds hlen htemp W hWK hWL
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    by_cases hW' : W' = ⊥
    · have := hc.sup_eq_top
      rwa [hW', sup_bot_eq] at this
    · exfalso
      have h := hc.inf_eq_bot
      have hf : f₀ ∈ W ⊓ W' := ⟨hmem W hWK hWL hW, hmem W' hW'K hW'L hW'⟩
      rw [h, Submodule.mem_bot] at hf
      exact hf₀ hf

/-- **Irreducibility from a cyclic vector of multiplicity one.** Let `ds` be a list of `n`
complex characters whose exponents all have the same real part, and let `f₀` be a nonzero
`U(n)`-finite function of `complexStandardModule n ds` such that every
`(𝔤𝔩_n(ℂ), U(n))`-submodule containing `f₀` is everything (`f₀` is cyclic), and every
`U(n)`-equivariant endomorphism maps `f₀` to a multiple of itself (the `U(n)`-type of `f₀`
occurs once and `f₀` spans its line under the endomorphisms). Then the module is irreducible. -/
def ComplexTemperedCyclicVectorStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
    ∀ f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n), f₀ ≠ 0 →
      (∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
        (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
        f₀ ∈ W → W = ⊤) →
      (∀ E : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
          kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
          E (complexStandardRep n ds k f) = complexStandardRep n ds k (E f)) →
        ∃ c : ℂ, E f₀ = c • f₀) →
      IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)

/-- The projection `P` onto `W` along a `(𝔤, K)`-stable complement `W'` maps `f₀` to `c f₀`;
for `c = 0` the vector `f₀` lies in `W'`, otherwise in `W`. -/
theorem complexTemperedCyclicVector : ComplexTemperedCyclicVectorStatement := by
  intro n ds hlen htemp f₀ hf₀ hcyc hmult
  refine ⟨nontrivial_of_ne f₀ 0 hf₀, fun W hWK hWL => ?_⟩
  obtain ⟨W', hW'K, hW'L, hc⟩ := complexTemperedComplement n ds hlen htemp W hWK hWL
  obtain ⟨c, hcP⟩ := hmult (W.projection W' hc)
    (fun k f => projection_comm hc _ (hWK k) (hW'K k) f)
  by_cases h0 : c = 0
  · left
    have hf : f₀ ∈ W' := by
      rw [← Submodule.projection_apply_eq_zero_iff hc, hcP, h0, zero_smul]
    have htop := hcyc W' hW'K hW'L hf
    have := hc.inf_eq_bot
    rwa [htop, inf_top_eq] at this
  · right
    refine hcyc W hWK hWL ?_
    have h1 : f₀ = c⁻¹ • W.projection W' hc f₀ := by
      rw [hcP, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [h1]
    exact W.smul_mem _ (Submodule.projection_apply_mem hc f₀)

/-- **Uniqueness of the Jacquet functional of evaluation at `1`.** For a list `ds` of `n`
complex characters whose exponents all have the same real part, every Jacquet functional on the
`U(n)`-finite functions of `complexStandardModule n ds` with the exponents
`κ_j(1) = 2 t_j + (n - 1) - 2 j` and `κ_j(i) = i l_j` of evaluation at `1`
(`ComplexSwapJacquet.kappa`) is a multiple of evaluation at `1`. -/
def ComplexTemperedJacquetUniqueStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (hn : ds.length = n),
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
    ∀ ℓ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ,
      IsComplexJacquetFunctional n (complexStandardLie n ds) ℓ
        (fun j => ComplexSwapJacquet.kappa ds hn j 1)
        (fun j => ComplexSwapJacquet.kappa ds hn j Complex.I) →
      ∃ c : ℂ, ℓ = c • kFiniteEval (complexStandardModule n ds) 1

/-- Uniqueness of the Jacquet functional gives scalar endomorphisms: for an endomorphism `E`,
`ev₁ ∘ E` is a Jacquet functional with the exponents of `ev₁`, so `ev₁ ∘ E = c ev₁`, and
`E f - c f` vanishes at every `k ∈ U(n)` after translation, hence is zero. -/
theorem complexTemperedEndScalar_of_jacquetUnique (hJ : ComplexTemperedJacquetUniqueStatement) :
    ComplexTemperedEndScalarStatement := by
  intro n ds hlen htemp E hEK hEL
  obtain ⟨c, hc⟩ := hJ n ds hlen htemp _ (isComplexJacquetFunctional_eval_comp hlen E hEL)
  refine ⟨c, fun f => ?_⟩
  rw [← sub_eq_zero]
  refine kFiniteEval_one_separating ds _ fun k => ?_
  have h1 := LinearMap.congr_fun hc (complexStandardRep n ds k f)
  rw [LinearMap.comp_apply, hEK, LinearMap.smul_apply, smul_eq_mul] at h1
  rw [map_sub, map_sub, map_smul, h1, map_smul, smul_eq_mul, sub_self]

end Langlands.Archimedean
