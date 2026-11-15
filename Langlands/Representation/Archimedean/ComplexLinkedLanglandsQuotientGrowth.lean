import Langlands.Representation.Archimedean.ComplexLinkedLanglandsQuotientDuality
import Langlands.Representation.Archimedean.ComplexJacquetFinite
import Langlands.Algebra.UniversalEnvelopingFiltration
import Mathlib.RingTheory.Finiteness.Bilinear

/-!
# A small submodule of the dual standard module from two growth bounds

`complexDualSubmoduleAnnihilator_of_growth` derives `ComplexDualSubmoduleAnnihilatorStatement`
from two growth statements:

* `ComplexStandardHolomorphicGrowthStatement`: the elements of degree `≤ d` of the holomorphic
  factor of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` act on the `U(n)`-finite principal series through at least
  `c (d + 1)^(n (n - 1))` linearly independent operators;
* `ComplexLinkedSmallGrowthStatement`: for a Langlands-ordered linked list, the dual standard
  module contains a nonzero finite-dimensional `U(n)`-stable subspace `E` with
  `dim U_d(𝔤) E ≤ C (d + 1)^(n (n - 1) - 1)`.

The proof uses the splitting `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) = 𝔤_hol ⊕ 𝔤_antihol` into two commuting ideals and
a dimension count.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open Langlands.Algebra.UniversalEnveloping
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

universe uL uV

namespace ComplexLinkedLanglandsQuotientGrowth

/-! ## The holomorphic and antiholomorphic factors -/

section Factors

variable {n : ℕ}

/-- The holomorphic part `½ (1 ⊗ X - i ⊗ iX)` of `X ∈ 𝔤𝔩_n(ℂ)` in `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. -/
def hol (X : Matrix (Fin n) (Fin n) ℂ) : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (2⁻¹ : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X - Complex.I ⊗ₜ[ℝ] (Complex.I • X))

/-- The antiholomorphic part `½ (1 ⊗ X + i ⊗ iX)` of `X ∈ 𝔤𝔩_n(ℂ)` in `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. -/
def antihol (X : Matrix (Fin n) (Fin n) ℂ) : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (2⁻¹ : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] (Complex.I • X))

theorem tmul_eq_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (c ⊗ₜ[ℝ] Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) = c • ((1 : ℂ) ⊗ₜ[ℝ] Z) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem hol_add_antihol (X : Matrix (Fin n) (Fin n) ℂ) :
    hol X + antihol X = (1 : ℂ) ⊗ₜ[ℝ] X := by
  rw [hol, antihol]
  module

theorem hol_add (X Y : Matrix (Fin n) (Fin n) ℂ) : hol (X + Y) = hol X + hol Y := by
  simp only [hol, smul_add, TensorProduct.tmul_add]
  module

-- `match_scalars` leaves goals that `ring_nf` closes or not, depending on the coefficient.
set_option linter.unnecessarySeqFocus false in
theorem hol_I_smul (X : Matrix (Fin n) (Fin n) ℂ) : hol (Complex.I • X) = Complex.I • hol X := by
  have hII : Complex.I • Complex.I • X = -X := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hol, hol, hII, TensorProduct.tmul_neg, tmul_eq_smul Complex.I X,
    tmul_eq_smul Complex.I (Complex.I • X)]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- `f (1 ⊗ Z) f (1 ⊗ W) - f (1 ⊗ W) f (1 ⊗ Z) = f (1 ⊗ ⁅Z, W⁆)` for a Lie algebra map `f` into
an associative algebra. -/
theorem hom_one_tmul_commutator {A : Type*} [Ring A] [Algebra ℂ A]
    (f : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ A) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    f ((1 : ℂ) ⊗ₜ[ℝ] Z) * f ((1 : ℂ) ⊗ₜ[ℝ] W) - f ((1 : ℂ) ⊗ₜ[ℝ] W) * f ((1 : ℂ) ⊗ₜ[ℝ] Z) =
      f ((1 : ℂ) ⊗ₜ[ℝ] (Z * W - W * Z)) := by
  have h := f.map_lie ((1 : ℂ) ⊗ₜ[ℝ] Z) ((1 : ℂ) ⊗ₜ[ℝ] W)
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket] at h
  exact h.symm

theorem comm_aux {A : Type*} [Ring A] [Algebra ℂ A] (a a' b b' c c' : A)
    (r1 : a * b = b * a + c) (r2 : a * b' = b' * a + c') (r3 : a' * b = b * a' + c')
    (r4 : a' * b' = b' * a' - c) :
    (2⁻¹ : ℂ) • (a - Complex.I • a') * ((2⁻¹ : ℂ) • (b + Complex.I • b')) =
      (2⁻¹ : ℂ) • (b + Complex.I • b') * ((2⁻¹ : ℂ) • (a - Complex.I • a')) := by
  have key : (a - Complex.I • a') * (b + Complex.I • b') =
      (b + Complex.I • b') * (a - Complex.I • a') := by
    have e : ∀ x : A, Complex.I • Complex.I • x = -x := fun x => by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, e, r1, r2, r3,
      r4, smul_add, smul_sub]
    abel
  rw [smul_mul_assoc, mul_smul_comm, key, smul_mul_assoc, mul_smul_comm, smul_comm]

/-- **The holomorphic and antiholomorphic factors commute** under every Lie algebra map into an
associative algebra. -/
theorem hom_hol_mul_antihol {A : Type*} [Ring A] [Algebra ℂ A]
    (f : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ A) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    f (hol X) * f (antihol Y) = f (antihol Y) * f (hol X) := by
  have hcomm : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, f ((1 : ℂ) ⊗ₜ[ℝ] Z) * f ((1 : ℂ) ⊗ₜ[ℝ] W) =
      f ((1 : ℂ) ⊗ₜ[ℝ] W) * f ((1 : ℂ) ⊗ₜ[ℝ] Z) + f ((1 : ℂ) ⊗ₜ[ℝ] (Z * W - W * Z)) :=
    fun Z W => by rw [← hom_one_tmul_commutator f Z W]; abel
  have e2 : X * (Complex.I • Y) - Complex.I • Y * X = Complex.I • (X * Y - Y * X) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  have e3 : Complex.I • X * Y - Y * (Complex.I • X) = Complex.I • (X * Y - Y * X) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  have e4 : Complex.I • X * (Complex.I • Y) - Complex.I • Y * (Complex.I • X) =
      -(X * Y - Y * X) := by
    simp only [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
    abel
  have r4 := hcomm (Complex.I • X) (Complex.I • Y)
  rw [e4, TensorProduct.tmul_neg, map_neg, ← sub_eq_add_neg] at r4
  have r2 := hcomm X (Complex.I • Y)
  rw [e2] at r2
  have r3 := hcomm (Complex.I • X) Y
  rw [e3] at r3
  have hh : f (hol X) = (2⁻¹ : ℂ) • (f ((1 : ℂ) ⊗ₜ[ℝ] X) -
      Complex.I • f ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • X))) := by
    rw [hol, map_smul, map_sub, tmul_eq_smul Complex.I, map_smul]
  have ha : f (antihol Y) = (2⁻¹ : ℂ) • (f ((1 : ℂ) ⊗ₜ[ℝ] Y) +
      Complex.I • f ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • Y))) := by
    rw [antihol, map_smul, map_add, tmul_eq_smul Complex.I, map_smul]
  rw [hh, ha]
  exact comm_aux _ _ _ _ _ _ (hcomm X Y) r2 r3 r4

/-- A complex matrix is `κ₁ + i κ₂` with `κ₁ = (X - Xᴴ)/2` and `κ₂ = -i (X + Xᴴ)/2`
skew-Hermitian. -/
theorem exists_skew_decomp (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ κ₁ κ₂ : Matrix (Fin n) (Fin n) ℂ, star κ₁ = -κ₁ ∧ star κ₂ = -κ₂ ∧
      X = κ₁ + Complex.I • κ₂ := by
  refine ⟨(2⁻¹ : ℂ) • (X - star X), (-(Complex.I * 2⁻¹) : ℂ) • (X + star X), ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.star_apply]
    try ring
  · ext i j
    simp [Matrix.star_apply]
    try ring
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (2⁻¹ * (X i j + (star X) i j)) * Complex.I_sq

end Factors

/-! ## The filtration of the holomorphic factor and filtered spans -/

section Filtration

variable (n : ℕ)

/-- The subalgebra of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` generated by the holomorphic factor. -/
def holAlg : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) :=
  Algebra.adjoin ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
    UniversalEnvelopingAlgebra.ι ℂ (hol X))

/-- The subalgebra of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` generated by the antiholomorphic factor. -/
def antiholAlg : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) :=
  Algebra.adjoin ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
    UniversalEnvelopingAlgebra.ι ℂ (antihol X))

/-- Elements of degree `≤ d` of the holomorphic factor: products of at most `d` elements
`ι (hol X)`, and their linear combinations. -/
def holFiltration (d : ℕ) :
    Submodule ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) :=
  (Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
    UniversalEnvelopingAlgebra.ι ℂ (hol X)) ⊔ 1) ^ d

variable {n}

theorem holFiltration_le_holAlg (d : ℕ) :
    holFiltration n d ≤ Subalgebra.toSubmodule (holAlg n) := by
  have hG : Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
      UniversalEnvelopingAlgebra.ι ℂ (hol X)) ⊔ 1 ≤ Subalgebra.toSubmodule (holAlg n) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.one_le.2 (one_mem (holAlg n)))
    rintro _ ⟨X, rfl⟩
    exact Algebra.subset_adjoin ⟨X, rfl⟩
  induction d with
  | zero => exact Submodule.one_le.2 (one_mem (holAlg n))
  | succ d ih =>
    rw [holFiltration, pow_succ]
    exact Submodule.mul_le.2 fun a ha b hb => (holAlg n).mul_mem (ih ha) (hG hb)

theorem holFiltration_le_degreeFiltration (d : ℕ) :
    holFiltration n d ≤ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) d := by
  have hG : Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n) ℂ =>
      UniversalEnvelopingAlgebra.ι ℂ (hol X)) ⊔ 1 ≤
        degreeOne ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) := by
    refine sup_le (Submodule.span_le.2 ?_) (one_le_degreeOne _ _)
    rintro _ ⟨X, rfl⟩
    exact generator_mem_degreeOne _ _ _
  induction d with
  | zero => rw [holFiltration, pow_zero, degreeFiltration_zero]
  | succ d ih =>
    rw [holFiltration, pow_succ, degreeFiltration, pow_succ]
    exact mul_le_mul' ih hG

instance holFiltration_finiteDimensional (d : ℕ) : FiniteDimensional ℂ (holFiltration n d) :=
  Submodule.finiteDimensional_of_le (holFiltration_le_degreeFiltration d)

end Filtration

variable {L : Type uL} [LieRing L] [LieAlgebra ℂ L] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The span `U_d(L) · E` of the vectors `u · e` with `u` of degree `≤ d` and `e ∈ E`. -/
def filtrationSpan (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (d : ℕ) (E : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.map₂ (envelopingAction π).toLinearMap (degreeFiltration ℂ L d) E

/-! ## The dimension count -/

/-- **Dimension count.** If the operators of a finite-dimensional space `P` span more dimensions
than `dim E · dim W`, where `W ⊇ P · E`, some element of `P` kills `E` but acts nonzero. -/
theorem exists_kill_of_finrank_lt {A : Type*} [Ring A] [Algebra ℂ A]
    (φ : A →ₐ[ℂ] Module.End ℂ V) (P : Submodule ℂ A) [FiniteDimensional ℂ P]
    (E W : Submodule ℂ V) [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (hW : ∀ v ∈ P, ∀ e ∈ E, φ v e ∈ W)
    (hlt : Module.finrank ℂ E * Module.finrank ℂ W <
      Module.finrank ℂ (P.map φ.toLinearMap)) :
    ∃ v ∈ P, (∀ e ∈ E, φ v e = 0) ∧ φ v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let Ψ : P →ₗ[ℂ] E →ₗ[ℂ] W :=
    LinearMap.mk₂ ℂ (fun (v : P) (e : E) => (⟨φ v e, hW v v.2 e e.2⟩ : W))
      (fun v₁ v₂ e => by ext; simp)
      (fun c v e => by ext; simp)
      (fun v e₁ e₂ => by ext; simp)
      (fun c v e => by ext; simp)
  let Φ : P →ₗ[ℂ] Module.End ℂ V := φ.toLinearMap ∘ₗ P.subtype
  have hker : LinearMap.ker Ψ ≤ LinearMap.ker Φ := by
    intro v hv
    have hv' : ∀ e ∈ E, φ v e = 0 := fun e he => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.1 hv) ⟨e, he⟩
      simpa [Ψ] using congrArg Subtype.val this
    exact LinearMap.mem_ker.2 (hcon v v.2 hv')
  have hrange : LinearMap.range Φ = P.map φ.toLinearMap := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  have h3 := Submodule.finrank_mono hker
  have h4 : Module.finrank ℂ (LinearMap.range Ψ) ≤ Module.finrank ℂ E * Module.finrank ℂ W := by
    rw [← Module.finrank_linearMap]
    exact Submodule.finrank_le _
  rw [← hrange] at hlt
  omega

/-! ## The diagonal argument -/

section Diagonal

variable {n : ℕ}

theorem ι_hol_mul_ι_antihol (X Y : Matrix (Fin n) (Fin n) ℂ) :
    UniversalEnvelopingAlgebra.ι ℂ (hol X) * UniversalEnvelopingAlgebra.ι ℂ (antihol Y) =
      UniversalEnvelopingAlgebra.ι ℂ (antihol Y) * UniversalEnvelopingAlgebra.ι ℂ (hol X) :=
  hom_hol_mul_antihol (UniversalEnvelopingAlgebra.ι ℂ) X Y

/-- Elements of the holomorphic and antiholomorphic subalgebras commute. -/
theorem holAlg_commute {a b : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)}
    (ha : a ∈ holAlg n) (hb : b ∈ antiholAlg n) : a * b = b * a := by
  have hgen : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      holAlg n ≤ Subalgebra.centralizer ℂ {UniversalEnvelopingAlgebra.ι ℂ (antihol Y)} := by
    intro Y
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (ι_hol_mul_ι_antihol X Y).symm
  have hb' : antiholAlg n ≤ Subalgebra.centralizer ℂ (holAlg n : Set _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨Y, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    have := (Subalgebra.mem_centralizer_iff ℂ).1 (hgen Y hg) _ rfl
    exact this.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hb' hb) a ha)

variable {ds : List ComplexCharacterData}

local notation "Vs" => kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

/-- Conjugation by `k ∈ U(n)` on `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. -/
def adK (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ[ℂ] (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.baseChange ℂ
    ((LinearMap.mulLeft ℝ (k : Matrix (Fin n) (Fin n) ℂ)).comp
      (LinearMap.mulRight ℝ (star k : Matrix (Fin n) (Fin n) ℂ)))

theorem rep_lie (k : Matrix.unitaryGroup (Fin n) ℂ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (v : Vs) : complexStandardRep n ds k (complexStandardLie n ds x v) =
      complexStandardLie n ds (adK k x) (complexStandardRep n ds k v) := by
  induction x using TensorProduct.inductionOn generalizing v with
  | tmul c X =>
    have hc : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
        (c ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) = c • ((1 : ℂ) ⊗ₜ Y) := fun Y => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hgk := (isComplexGKModule_complexStandardModule n ds).2.2.2 k X v
    have hconj : (LinearMap.mulLeft ℝ (k : Matrix (Fin n) (Fin n) ℂ) ∘ₗ
        LinearMap.mulRight ℝ (star k : Matrix (Fin n) (Fin n) ℂ)) X =
          (k : Matrix (Fin n) (Fin n) ℂ) * X * (star k : Matrix (Fin n) (Fin n) ℂ) := by
      simp [mul_assoc]
    rw [adK, LinearMap.baseChange_tmul, hconj, hc, hc, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul, hgk]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]

theorem rep_envelopingAction (k : Matrix.unitaryGroup (Fin n) ℂ)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) :
    ∃ u' : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ v : Vs,
      complexStandardRep n ds k (envelopingAction (complexStandardLie n ds) u v) =
        envelopingAction (complexStandardLie n ds) u' (complexStandardRep n ds k v) := by
  induction u using InfinitesimalCharacter.envInduction with
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ r, fun v => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι x =>
    refine ⟨UniversalEnvelopingAlgebra.ι ℂ (adK k x), fun v => ?_⟩
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
    exact rep_lie k x v
  | mul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' * b', fun v => ?_⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha', hb']
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun v => ?_⟩
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha', hb']

/-- **The diagonal argument.** Let `E` be a `U(n)`-stable subspace and `v` an element of the
holomorphic subalgebra killing `E`. Then `v` kills the `(𝔤, K)`-submodule `U(𝔤) · E`. -/
theorem kills_span_of_kills (E : Submodule ℂ Vs)
    (hEK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ e ∈ E, complexStandardRep n ds k e ∈ E)
    {v : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)} (hv : v ∈ holAlg n)
    (hvE : ∀ e ∈ E, envelopingAction (complexStandardLie n ds) v e = 0) :
    ∀ s ∈ Submodule.map₂ (envelopingAction (complexStandardLie n ds)).toLinearMap ⊤ E,
      envelopingAction (complexStandardLie n ds) v s = 0 := by
  set φ := envelopingAction (complexStandardLie n ds)
  set π := complexStandardLie n ds
  let M : Submodule ℂ Vs :=
    Submodule.map₂ φ.toLinearMap (Subalgebra.toSubmodule (antiholAlg n)) E
  have hEM : E ≤ M := fun e he => by
    have := Submodule.apply_mem_map₂ φ.toLinearMap
      ((Subalgebra.mem_toSubmodule (antiholAlg n)).2 (one_mem _)) he
    simpa [φ] using this
  -- `M` is stable under the antiholomorphic subalgebra.
  have hMb : ∀ b ∈ antiholAlg n, ∀ m ∈ M, φ b m ∈ M := by
    intro b hb m hm
    have hle : M ≤ M.comap (φ b) := Submodule.map₂_le.2 fun b' hb' e he => ?_
    · exact hle hm
    rw [Submodule.mem_comap]
    change φ b (φ b' e) ∈ M
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.apply_mem_map₂ _ ((antiholAlg n).mul_mem hb hb') he
  have hanti : ∀ X : Matrix (Fin n) (Fin n) ℂ, UniversalEnvelopingAlgebra.ι ℂ (antihol X) ∈
      antiholAlg n := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hholE : ∀ X : Matrix (Fin n) (Fin n) ℂ, ∀ e ∈ E, π (hol X) e ∈ M := by
    have hk : ∀ κ : Matrix (Fin n) (Fin n) ℂ, star κ = -κ → ∀ e ∈ E, π (hol κ) e ∈ M := by
      intro κ hκ e he
      have hdec : hol κ = (1 : ℂ) ⊗ₜ[ℝ] κ - antihol κ := by
        rw [← hol_add_antihol, add_sub_cancel_right]
      rw [hdec, map_sub, LinearMap.sub_apply]
      refine M.sub_mem (hEM (ComplexJacquetFinite.skew_stable
        (isComplexGKModule_complexStandardModule n ds) E hEK κ hκ e he)) ?_
      have := hMb _ (hanti κ) e (hEM he)
      simpa [φ, π] using this
    intro X e he
    obtain ⟨κ₁, κ₂, h₁, h₂, rfl⟩ := exists_skew_decomp X
    rw [hol_add, hol_I_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact M.add_mem (hk κ₁ h₁ e he) (M.smul_mem _ (hk κ₂ h₂ e he))
  -- `M` is stable under `π`.
  have hMπ : ∀ x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ, ∀ m ∈ M, π x m ∈ M := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c X =>
      intro m hm
      have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) = c • ((1 : ℂ) ⊗ₜ X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, LinearMap.smul_apply, ← hol_add_antihol, map_add, LinearMap.add_apply]
      refine M.smul_mem _ (M.add_mem ?_ ?_)
      · have hle : M ≤ M.comap (π (hol X)) := Submodule.map₂_le.2 fun b hb e he => ?_
        · exact hle hm
        rw [Submodule.mem_comap]
        change π (hol X) (φ b e) ∈ M
        have hcomm := holAlg_commute (n := n)
          (Algebra.subset_adjoin ⟨X, rfl⟩ : UniversalEnvelopingAlgebra.ι ℂ (hol X) ∈ holAlg n) hb
        have e1 : π (hol X) (φ b e) = φ b (π (hol X) e) := by
          have : φ (UniversalEnvelopingAlgebra.ι ℂ (hol X) * b) e =
              φ (b * UniversalEnvelopingAlgebra.ι ℂ (hol X)) e := by rw [hcomm]
          simpa [φ, π, map_mul, Module.End.mul_apply] using this
        rw [e1]
        exact hMb b hb _ (hholE X e he)
      · have := hMb _ (hanti X) m hm
        simpa [φ, π] using this
    | add x y hx hy =>
      intro m hm
      rw [map_add, LinearMap.add_apply]
      exact M.add_mem (hx m hm) (hy m hm)
  -- `M` contains `U(𝔤) · E`.
  have hall : ∀ u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ),
      ∀ m ∈ M, φ u m ∈ M := by
    intro u
    induction u using InfinitesimalCharacter.envInduction with
    | algebraMap r =>
      intro m hm
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact M.smul_mem r hm
    | ι x =>
      intro m hm
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      exact hMπ x m hm
    | mul a b ha hb =>
      intro m hm
      rw [map_mul, Module.End.mul_apply]
      exact ha _ (hb m hm)
    | add a b ha hb =>
      intro m hm
      rw [map_add, LinearMap.add_apply]
      exact M.add_mem (ha m hm) (hb m hm)
  -- `v` kills `M`.
  have hvM : M ≤ LinearMap.ker (φ v) := Submodule.map₂_le.2 fun b hb e he => by
    rw [LinearMap.mem_ker]
    change φ v (φ b e) = 0
    rw [← Module.End.mul_apply, ← map_mul, holAlg_commute hv hb, map_mul,
      Module.End.mul_apply, hvE e he, map_zero]
  intro s hs
  exact LinearMap.mem_ker.1
    (hvM (Submodule.map₂_le.2 (fun u _ e he => hall u e (hEM he)) hs))

end Diagonal

end ComplexLinkedLanglandsQuotientGrowth

open ComplexLinkedLanglandsQuotientGrowth

/-! ## The growth statements and the reduction -/

/-- **Growth of the holomorphic action on a complex principal series.** For every `n` and every
list `ds` of complex characters, the elements of degree `≤ d` of the holomorphic factor of
`U(ℂ ⊗_ℝ 𝔤𝔩_n(ℂ))` act on the `U(n)`-finite functions of the standard module of `ds` through a
space of operators of dimension at least `c (d + 1)^(n (n - 1))`, for some `c > 0`. -/
def ComplexStandardHolomorphicGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ,
    c * ((d : ℝ) + 1) ^ (n * (n - 1)) ≤
      (Module.finrank ℂ ((holFiltration n d).map
        (envelopingAction (complexStandardLie n ds)).toLinearMap) : ℝ)

/-- **Small growth in the dual of a linked standard module.** For a Langlands-ordered list `ds`
of `n` complex characters, two of which are linked, and a list `ds'` of pointwise inverse
position characters, the `U(n)`-finite functions of the standard module of `ds'` contain a
nonzero finite-dimensional `U(n)`-stable subspace `E` such that the span of `U_d(𝔤) · E` has
dimension at most `C (d + 1)^(n (n - 1) - 1)`. -/
def ComplexLinkedSmallGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds ds' : List ComplexCharacterData), ds.length = n → IsComplexLanglandsOrdered ds →
    ¬ IsComplexUnlinked ds →
    (∀ (i : ℕ) (z : ℂˣ), complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1) →
      ∃ E : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
        E ≠ ⊥ ∧ FiniteDimensional ℂ E ∧
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ e ∈ E, complexStandardRep n ds' k e ∈ E) ∧
        ∃ C : ℝ, ∀ d : ℕ,
          (Module.finrank ℂ (filtrationSpan (complexStandardLie n ds') d E) : ℝ) ≤
            C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1)

theorem two_le_of_not_unlinked {n : ℕ} {ds : List ComplexCharacterData} (hlen : ds.length = n)
    (hlink : ¬ IsComplexUnlinked ds) : 2 ≤ n := by
  rcases ds with _ | ⟨a, _ | ⟨b, l⟩⟩
  · exact absurd List.Pairwise.nil hlink
  · exact absurd (List.pairwise_singleton _ a) hlink
  · rw [← hlen]
    simp

/-- **The reduction.** The two growth statements give a small submodule of the dual standard
module. -/
theorem complexDualSubmoduleAnnihilator_of_growth
    (hLo : ComplexStandardHolomorphicGrowthStatement) (hUp : ComplexLinkedSmallGrowthStatement) :
    ComplexDualSubmoduleAnnihilatorStatement := by
  intro n ds ds' hlen hord hlink hχ
  obtain ⟨E, hE0, hEfin, hEK, C, hC⟩ := hUp n ds ds' hlen hord hlink hχ
  obtain ⟨c, hc, hcd⟩ := hLo n ds'
  have hn := two_le_of_not_unlinked hlen hlink
  set φ := envelopingAction (complexStandardLie n ds')
  set N := n * (n - 1) with hN
  have hN1 : N - 1 + 1 = N := by
    have : 1 ≤ N := by
      rw [hN]
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  obtain ⟨d, hd⟩ := exists_nat_gt ((Module.finrank ℂ E : ℝ) * C / c)
  let W := Submodule.map₂ φ.toLinearMap (holFiltration n d) E
  have : FiniteDimensional ℂ (filtrationSpan (complexStandardLie n ds') d E) :=
    Module.Finite.iff_fg.2 ((degreeFiltration_fg ℂ _ d).map₂ _ (Module.Finite.iff_fg.1 hEfin))
  have hWle : W ≤ filtrationSpan (complexStandardLie n ds') d E :=
    Submodule.map₂_le_map₂_left (holFiltration_le_degreeFiltration d)
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
  have hWdim : (Module.finrank ℂ W : ℝ) ≤ C * ((d : ℝ) + 1) ^ (N - 1) :=
    le_trans (by exact_mod_cast Submodule.finrank_mono hWle) (hC d)
  have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ (N - 1) := by positivity
  have hlt : (Module.finrank ℂ E : ℝ) * Module.finrank ℂ W <
      Module.finrank ℂ ((holFiltration n d).map φ.toLinearMap) := by
    have h1 : (Module.finrank ℂ E : ℝ) * Module.finrank ℂ W ≤
        (Module.finrank ℂ E : ℝ) * (C * ((d : ℝ) + 1) ^ (N - 1)) :=
      mul_le_mul_of_nonneg_left hWdim (Nat.cast_nonneg _)
    have h2 : (Module.finrank ℂ E : ℝ) * C < c * ((d : ℝ) + 1) := by
      rw [div_lt_iff₀ hc] at hd
      nlinarith
    have h3 : c * ((d : ℝ) + 1) ^ N = c * ((d : ℝ) + 1) * ((d : ℝ) + 1) ^ (N - 1) := by
      conv_lhs => rw [← hN1]
      rw [pow_succ]
      ring
    calc (Module.finrank ℂ E : ℝ) * Module.finrank ℂ W
        ≤ (Module.finrank ℂ E : ℝ) * C * ((d : ℝ) + 1) ^ (N - 1) := by
          rw [mul_assoc]; exact h1
      _ < c * ((d : ℝ) + 1) * ((d : ℝ) + 1) ^ (N - 1) :=
          mul_lt_mul_of_pos_right h2 hpos
      _ = c * ((d : ℝ) + 1) ^ N := h3.symm
      _ ≤ _ := hcd d
  have hlt' : Module.finrank ℂ E * Module.finrank ℂ W <
      Module.finrank ℂ ((holFiltration n d).map φ.toLinearMap) := by
    exact_mod_cast hlt
  obtain ⟨v, hvP, hvE, hv0⟩ := exists_kill_of_finrank_lt φ (holFiltration n d) E W
    (fun v hv e he => Submodule.apply_mem_map₂ _ hv he) hlt'
  -- The submodule `U(𝔤) · E`.
  let S := Submodule.map₂ φ.toLinearMap ⊤ E
  have hES : E ≤ S := fun e he => by
    have := Submodule.apply_mem_map₂ φ.toLinearMap (Submodule.mem_top (x := 1)) he
    simpa [φ] using this
  refine ⟨S, ⟨fun k s hs => ?_, fun x s hs => ?_⟩, ?_, v, ?_, hv0⟩
  · have hle : S ≤ S.comap (complexStandardRep n ds' k) :=
      Submodule.map₂_le.2 fun u _ e he => ?_
    · exact hle hs
    rw [Submodule.mem_comap]
    obtain ⟨u', hu'⟩ := rep_envelopingAction (ds := ds') k u
    change complexStandardRep n ds' k (φ u e) ∈ S
    rw [hu']
    exact Submodule.apply_mem_map₂ _ Submodule.mem_top (hEK k e he)
  · have hle : S ≤ S.comap (complexStandardLie n ds' x) :=
      Submodule.map₂_le.2 fun u _ e he => ?_
    · exact hle hs
    rw [Submodule.mem_comap]
    change complexStandardLie n ds' x (φ u e) ∈ S
    have : complexStandardLie n ds' x (φ u e) = φ (UniversalEnvelopingAlgebra.ι ℂ x * u) e := by
      rw [map_mul, Module.End.mul_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
    rw [this]
    exact Submodule.apply_mem_map₂ _ Submodule.mem_top he
  · intro hS
    exact hE0 (eq_bot_iff.2 (hS ▸ hES))
  · exact kills_span_of_kills E hEK (holFiltration_le_holAlg d hvP) hvE

end Langlands.Archimedean
