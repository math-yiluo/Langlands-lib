import Langlands.Algebra.LieCasimir
import Langlands.Global.ArchimedeanCartanTraceForm
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The actual matrix trace Casimir in the complex enveloping center -/

noncomputable section
universe u t
open Module
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : FiniteDimensional ℝ (RealLieAlgebra K n) :=
  FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
    (realLieAlgebraToMatrix K n).injective

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Each actual real matrix direction, in the genuine complex enveloping algebra. -/
def realEnvelopingGenerator : RealLieAlgebra K n →ₗ⁅ℝ⁆ EnvelopingAlgebra K n :=
  { ((envelopingGenerator K n).toLinearMap.restrictScalars ℝ).comp
      (complexify K n).toLinearMap with
    map_lie' := by
      intro X Y
      change envelopingGenerator K n (complexify K n ⁅X, Y⁆) =
        ⁅envelopingGenerator K n (complexify K n X),
          envelopingGenerator K n (complexify K n Y)⁆
      rw [(complexify K n).map_lie, (envelopingGenerator K n).map_lie] }

omit [NumberField K] in
@[simp]
theorem realEnvelopingGenerator_apply (X : RealLieAlgebra K n) :
    realEnvelopingGenerator K n X =
      envelopingGenerator K n ((1 : ℂ) ⊗ₜ[ℝ] X) := rfl

omit [NumberField K] in
theorem envelopingGenerator_tmul (z : ℂ) (X : RealLieAlgebra K n) :
    envelopingGenerator K n (z ⊗ₜ[ℝ] X) = z • realEnvelopingGenerator K n X := by
  rw [realEnvelopingGenerator_apply, ← map_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- The real trace-form Casimir image in the original complex enveloping algebra. -/
def matrixCasimir : EnvelopingAlgebra K n :=
  Langlands.Algebra.LieCasimir.casimirImage (matrixTraceForm K n)
    (matrixTraceForm_nondegenerate K n) (Module.finBasis ℝ (RealLieAlgebra K n))
    (realEnvelopingGenerator K n)

theorem matrixCasimir_eq_sum {ι : Type t} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ (RealLieAlgebra K n)) :
    matrixCasimir K n = ∑ i, realEnvelopingGenerator K n (b i) *
      realEnvelopingGenerator K n
        ((matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n) b i) :=
  Langlands.Algebra.LieCasimir.casimirImage_basis_independent _ _
    (Module.finBasis ℝ (RealLieAlgebra K n)) b (realEnvelopingGenerator K n)

theorem matrixCasimir_commutes_real_generator (X : RealLieAlgebra K n) :
    realEnvelopingGenerator K n X * matrixCasimir K n =
      matrixCasimir K n * realEnvelopingGenerator K n X :=
  Langlands.Algebra.LieCasimir.casimirImage_commutes_generator _ _
    (matrixTraceForm_lie K n) (Module.finBasis ℝ (RealLieAlgebra K n))
    (realEnvelopingGenerator K n) X

theorem matrixCasimir_mem_center :
    matrixCasimir K n ∈ Subalgebra.center ℂ (EnvelopingAlgebra K n) := by
  let S := Subalgebra.centralizer ℂ {matrixCasimir K n}
  have hreal (X : RealLieAlgebra K n) : realEnvelopingGenerator K n X ∈ S := by
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (matrixCasimir_commutes_real_generator K n X).symm
  have hcomplex (X : ComplexLieAlgebra K n) : envelopingGenerator K n X ∈ S := by
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      rw [envelopingGenerator_tmul]
      exact S.smul_mem (hreal X) z
    | add X Y hX hY =>
      simpa only [map_add] using S.add_mem hX hY
  have hle : Algebra.adjoin ℂ (Set.range (envelopingGenerator K n)) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨X, rfl⟩
    exact hcomplex X
  rw [Subalgebra.mem_center_iff]
  intro a
  have ha : a ∈ Algebra.adjoin ℂ (Set.range (envelopingGenerator K n)) := by
    change a ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra K n → EnvelopingAlgebra K n))
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  exact ((Subalgebra.mem_centralizer_iff ℂ).mp (hle ha) _
    (Set.mem_singleton _)).symm

/-- The same Casimir as an element of the published genuine complex center. -/
def matrixCentralCasimir : EnvelopingCenter K n :=
  ⟨matrixCasimir K n, matrixCasimir_mem_center K n⟩

@[simp]
theorem centerInclusion_matrixCentralCasimir :
    centerInclusion K n (matrixCentralCasimir K n) = matrixCasimir K n := rfl

private theorem exists_cartan_normalized_basis
    (S : Submodule ℝ (RealLieAlgebra K n)) :
    ∃ b : Basis (Fin (Module.finrank ℝ S)) ℝ S, ∀ i j,
      cartanPositiveForm K n (b i) (b j) = if i = j then 1 else 0 := by
  classical
  let Q := (cartanPositiveForm K n).restrict S
  have hQ : Q.IsSymm := ⟨fun X Y => cartanPositiveForm_symm K n X Y⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hQ)
  have hpos (i : Fin (Module.finrank ℝ S)) : 0 < Q (b i) (b i) := by
    exact cartanPositiveForm_self_pos K n (X := (b i : RealLieAlgebra K n))
      (fun h => b.ne_zero i (Subtype.ext h))
  let c : Fin (Module.finrank ℝ S) → ℝ := fun i => (Real.sqrt (Q (b i) (b i)))⁻¹
  have hc (i : Fin (Module.finrank ℝ S)) : IsUnit (c i) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hpos i))))
  refine ⟨b.isUnitSMul hc, ?_⟩
  intro i j
  change Q ((b.isUnitSMul hc) i) ((b.isUnitSMul hc) j) = _
  rw [Basis.isUnitSMul_apply, Basis.isUnitSMul_apply]
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    dsimp [c]
    have hs := Real.sq_sqrt (le_of_lt (hpos i))
    have hn : Real.sqrt (Q (b i) (b i)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hpos i))
    field_simp
    nlinarith
  · rw [ite_eq_right hij, hb hij]
    simp

/-- A finite normalized basis for the actual positive Cartan form restricted
to an arbitrary real matrix subspace. -/
def cartanNormalizedBasis (S : Submodule ℝ (RealLieAlgebra K n)) :
    Basis (Fin (Module.finrank ℝ S)) ℝ S :=
  (exists_cartan_normalized_basis K n S).choose

theorem cartanNormalizedBasis_pair (S : Submodule ℝ (RealLieAlgebra K n))
    (i j : Fin (Module.finrank ℝ S)) :
    cartanPositiveForm K n (cartanNormalizedBasis K n S i)
      (cartanNormalizedBasis K n S j) = if i = j then 1 else 0 :=
  (exists_cartan_normalized_basis K n S).choose_spec i j

/-- The actual compact and complementary normalized basis index sets. -/
abbrev CartanBasisIndex :=
  Fin (Module.finrank ℝ (compactLieSubalgebra K n)) ⊕
    Fin (Module.finrank ℝ (cartanComplement K n))

def compactCartanBasis :
    Basis (Fin (Module.finrank ℝ (compactLieSubalgebra K n))) ℝ
      (compactLieSubalgebra K n) :=
  cartanNormalizedBasis K n (compactLieSubalgebra K n).toSubmodule

def complementaryCartanBasis :
    Basis (Fin (Module.finrank ℝ (cartanComplement K n))) ℝ
      (cartanComplement K n) :=
  cartanNormalizedBasis K n (cartanComplement K n)

/-- A normalized real basis containing all compact and complementary directions. -/
def cartanAdaptedBasis : Basis (CartanBasisIndex K n) ℝ (RealLieAlgebra K n) :=
  ((compactCartanBasis K n).prod (complementaryCartanBasis K n)).map
    (cartanDecomposition K n).symm

@[simp]
theorem cartanAdaptedBasis_inl (i : Fin (Module.finrank ℝ (compactLieSubalgebra K n))) :
    cartanAdaptedBasis K n (Sum.inl i) =
      (compactCartanBasis K n i : RealLieAlgebra K n) := by
  simp [cartanAdaptedBasis, Basis.prod_apply, cartanDecomposition_symm_apply]

@[simp]
theorem cartanAdaptedBasis_inr (i : Fin (Module.finrank ℝ (cartanComplement K n))) :
    cartanAdaptedBasis K n (Sum.inr i) =
      (complementaryCartanBasis K n i : RealLieAlgebra K n) := by
  simp [cartanAdaptedBasis, Basis.prod_apply, cartanDecomposition_symm_apply]

theorem cartanAdaptedBasis_pair (i j : CartanBasisIndex K n) :
    cartanPositiveForm K n (cartanAdaptedBasis K n i) (cartanAdaptedBasis K n j) =
      if i = j then 1 else 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simpa only [cartanAdaptedBasis_inl, Sum.inl.injEq, compactCartanBasis] using
        cartanNormalizedBasis_pair K n (compactLieSubalgebra K n).toSubmodule i j
    | inr j =>
      simpa only [cartanAdaptedBasis_inl, cartanAdaptedBasis_inr, Sum.inl_ne_inr,
        ite_false] using cartanPositiveForm_compact_complement K n
          (compactCartanBasis K n i) (complementaryCartanBasis K n j)
          (compactCartanBasis K n i).property (complementaryCartanBasis K n j).property
  | inr i =>
    cases j with
    | inl j =>
      simpa only [cartanAdaptedBasis_inl, cartanAdaptedBasis_inr, Sum.inr_ne_inl,
        ite_false] using cartanPositiveForm_complement_compact K n
          (complementaryCartanBasis K n i) (compactCartanBasis K n j)
          (complementaryCartanBasis K n i).property (compactCartanBasis K n j).property
    | inr j =>
      simpa only [cartanAdaptedBasis_inr, Sum.inr.injEq, complementaryCartanBasis] using
        cartanNormalizedBasis_pair K n (cartanComplement K n) i j

theorem matrixTraceForm_dual_cartanAdaptedBasis (i : CartanBasisIndex K n) :
    (matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n)
      (cartanAdaptedBasis K n) i = star (cartanAdaptedBasis K n i) := by
  have h : ⇑((matrixTraceForm K n).dualBasis (matrixTraceForm_nondegenerate K n)
      (cartanAdaptedBasis K n)) = fun j => star (cartanAdaptedBasis K n j) := by
    apply (LinearMap.BilinForm.dualBasis_eq_iff _ _ _).mpr
    intro i j
    rw [matrixTraceForm_symm, ← cartanPositiveForm_apply, cartanAdaptedBasis_pair]
  exact congrFun h i

@[simp]
theorem star_compactCartanBasis
    (i : Fin (Module.finrank ℝ (compactLieSubalgebra K n))) :
    star (compactCartanBasis K n i : RealLieAlgebra K n) =
      -(compactCartanBasis K n i : RealLieAlgebra K n) :=
  (mem_compactLieSubalgebra K n _).mp (compactCartanBasis K n i).property

@[simp]
theorem star_complementaryCartanBasis
    (i : Fin (Module.finrank ℝ (cartanComplement K n))) :
    star (complementaryCartanBasis K n i : RealLieAlgebra K n) =
      (complementaryCartanBasis K n i : RealLieAlgebra K n) :=
  (mem_cartanComplement K n _).mp (complementaryCartanBasis K n i).property

/-- The sum of squares of the actual normalized compact real generators. -/
def compactCartanSquareSum : EnvelopingAlgebra K n :=
  ∑ i, realEnvelopingGenerator K n (compactCartanBasis K n i) *
    realEnvelopingGenerator K n (compactCartanBasis K n i)

/-- The sum of squares of the actual normalized complementary real generators. -/
def complementaryCartanSquareSum : EnvelopingAlgebra K n :=
  ∑ i, realEnvelopingGenerator K n (complementaryCartanBasis K n i) *
    realEnvelopingGenerator K n (complementaryCartanBasis K n i)

/-- The sum of squares of all actual real directions in the normalized Cartan basis. -/
def cartanSquareSum : EnvelopingAlgebra K n :=
  ∑ i, realEnvelopingGenerator K n (cartanAdaptedBasis K n i) *
    realEnvelopingGenerator K n (cartanAdaptedBasis K n i)

theorem compactCartanSquareSum_mem :
    compactCartanSquareSum K n ∈ compactEnvelopingSubalgebra K n := by
  have hgen (X : compactLieSubalgebra K n) :
      realEnvelopingGenerator K n X ∈ compactEnvelopingSubalgebra K n :=
    compactEnvelopingGenerator_mem K n ((1 : ℂ) ⊗ₜ[ℝ] X)
  exact (compactEnvelopingSubalgebra K n).sum_mem fun i _ =>
    (compactEnvelopingSubalgebra K n).mul_mem
      (hgen (compactCartanBasis K n i)) (hgen (compactCartanBasis K n i))

/-- The compact square sum, in the original generated complex compact subalgebra. -/
def compactCartanElement : compactEnvelopingSubalgebra K n :=
  ⟨compactCartanSquareSum K n, compactCartanSquareSum_mem K n⟩

@[simp]
theorem compactCartanElement_val :
    (compactCartanElement K n : EnvelopingAlgebra K n) = compactCartanSquareSum K n := rfl

theorem matrixCasimir_eq_complementary_sub_compact :
    matrixCasimir K n =
      complementaryCartanSquareSum K n - compactCartanSquareSum K n := by
  rw [matrixCasimir_eq_sum K n (cartanAdaptedBasis K n)]
  simp only [matrixTraceForm_dual_cartanAdaptedBasis, Fintype.sum_sum_type,
    cartanAdaptedBasis_inl, cartanAdaptedBasis_inr, star_compactCartanBasis,
    star_complementaryCartanBasis, map_neg, mul_neg, Finset.sum_neg_distrib]
  exact neg_add_eq_sub _ _

theorem cartanSquareSum_eq_add :
    cartanSquareSum K n =
      compactCartanSquareSum K n + complementaryCartanSquareSum K n := by
  simp only [cartanSquareSum, Fintype.sum_sum_type, cartanAdaptedBasis_inl,
    cartanAdaptedBasis_inr, compactCartanSquareSum, complementaryCartanSquareSum]

theorem cartanSquareSum_eq_casimir_add_twice_compact :
    cartanSquareSum K n = matrixCasimir K n + (2 : ℂ) • compactCartanSquareSum K n := by
  rw [cartanSquareSum_eq_add, matrixCasimir_eq_complementary_sub_compact, two_smul]
  abel

/-- The full square sum is the actual central Casimir plus a compact-algebra element. -/
theorem cartanSquareSum_eq_central_add_compact :
    cartanSquareSum K n = centerInclusion K n (matrixCentralCasimir K n) +
      (2 : ℂ) • (compactCartanElement K n : EnvelopingAlgebra K n) :=
  cartanSquareSum_eq_casimir_add_twice_compact K n

end Langlands.Global.ArchimedeanGL
