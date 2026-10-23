import Langlands.Global.Adelic
import Langlands.Global.FiniteAdelicGL.StandardIntegralStatement

/-!
# Finite local factors of the adelic general linear group

Projection evaluates matrix entries at a finite place. Inclusion inserts a
matrix at that place and the identity matrix elsewhere.
-/

noncomputable section

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual general linear group over a finite completion. -/
abbrev FiniteLocalGL (v : FinitePlace K) :=
  Matrix.GeneralLinearGroup (Fin n) (FiniteCompletion K v)

namespace FiniteAdelicGL

open scoped RestrictedProduct

local instance : DecidableEq (FinitePlace K) := Classical.decEq _

private def localEval (v : FinitePlace K) : FiniteAdeles K →+* FiniteCompletion K v where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation at one finite place, on matrix units and their inverses. -/
def localProjection (v : FinitePlace K) :
    FiniteAdelicGL K n →ₜ* FiniteLocalGL K n v where
  __ := Matrix.GeneralLinearGroup.map
    (localEval K v)
  continuous_toFun := (RestrictedProduct.continuous_eval v).generalLinearGroup_map

@[simp]
theorem localProjection_apply (v : FinitePlace K) (g : FiniteAdelicGL K n)
    (i j : Fin n) : localProjection K n v g i j = g i j v := rfl

private def singleMatrix (v : FinitePlace K)
    (A : Matrix (Fin n) (Fin n) (FiniteCompletion K v)) :
    Matrix (Fin n) (Fin n) (FiniteAdeles K) :=
  fun i j => ⟨fun w =>
    Pi.mulSingle (M := fun w => Matrix (Fin n) (Fin n) (FiniteCompletion K w)) v A w i j,
    by
      filter_upwards [show {v}ᶜ ∈ Filter.cofinite by simp] with w hw
      have h : w ≠ v := by simpa using hw
      simp only [Pi.mulSingle_eq_of_ne h, Matrix.one_apply]
      split_ifs <;> simp⟩

private theorem eval_singleMatrix (v w : FinitePlace K)
    (A : Matrix (Fin n) (Fin n) (FiniteCompletion K v)) :
    (localEval K w).mapMatrix
        (singleMatrix K n v A) =
      Pi.mulSingle (M := fun w => Matrix (Fin n) (Fin n) (FiniteCompletion K w)) v A w :=
  rfl

private theorem matrix_ext {A B : Matrix (Fin n) (Fin n) (FiniteAdeles K)}
    (h : ∀ w, (localEval K w).mapMatrix A =
      (localEval K w).mapMatrix B) :
    A = B := by
  apply Matrix.ext
  intro i j
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro w
  exact congrArg (fun C => C i j) (h w)

private def singleMatrixHom (v : FinitePlace K) :
    Matrix (Fin n) (Fin n) (FiniteCompletion K v) →*
      Matrix (Fin n) (Fin n) (FiniteAdeles K) where
  toFun := singleMatrix K n v
  map_one' := by
    apply matrix_ext K n
    intro w
    rw [eval_singleMatrix, map_one, Pi.mulSingle_one]
    rfl
  map_mul' A B := by
    apply matrix_ext K n
    intro w
    rw [map_mul, eval_singleMatrix, eval_singleMatrix, eval_singleMatrix,
      Pi.mulSingle_mul]
    rfl

private theorem continuous_singleMatrix (v : FinitePlace K) :
    Continuous (singleMatrix K n v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let S : Set (FinitePlace K) := {v}ᶜ
  let f : Matrix (Fin n) (Fin n) (FiniteCompletion K v) →
      Πʳ w : FinitePlace K, [FiniteCompletion K w, w.adicCompletionIntegers K]_[Filter.principal S] :=
    fun A => ⟨fun w =>
      Pi.mulSingle (M := fun w => Matrix (Fin n) (Fin n) (FiniteCompletion K w)) v A w i j,
      fun w hw => by
        have h : w ≠ v := by simpa [S] using hw
        change Pi.mulSingle (M := fun w => Matrix (Fin n) (Fin n) (FiniteCompletion K w))
          v A w i j ∈ w.adicCompletionIntegers K
        simp only [Pi.mulSingle_eq_of_ne h, Matrix.one_apply]
        split_ifs <;> simp⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun A : Matrix (Fin n) (Fin n) (FiniteCompletion K v) =>
      Pi.mulSingle (M := fun w => Matrix (Fin n) (Fin n) (FiniteCompletion K w)) v A w i j)
    by_cases h : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id.matrix_elem i j
    · simpa only [Pi.mulSingle_eq_of_ne h] using
        (continuous_const : Continuous (fun _ : Matrix (Fin n) (Fin n) (FiniteCompletion K v) =>
          (1 : Matrix (Fin n) (Fin n) (FiniteCompletion K w)) i j))
  have hS : Filter.cofinite ≤ Filter.principal S := by simp [S]
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

/-- Insert a local matrix unit, with identity matrix at all other finite places. -/
def localInclusion (v : FinitePlace K) :
    FiniteLocalGL K n v →ₜ* FiniteAdelicGL K n where
  __ := Units.map (singleMatrixHom K n v)
  continuous_toFun := (continuous_singleMatrix K n v).units_map _

@[simp]
theorem localProjection_localInclusion (v : FinitePlace K) (g : FiniteLocalGL K n v) :
    localProjection K n v (localInclusion K n v g) = g := by
  apply Units.ext
  change (localEval K v).mapMatrix (singleMatrix K n v g.val) = g.val
  rw [eval_singleMatrix, Pi.mulSingle_eq_same]

theorem localProjection_localInclusion_of_ne (v w : FinitePlace K) (h : w ≠ v)
    (g : FiniteLocalGL K n v) :
    localProjection K n w (localInclusion K n v g) = 1 := by
  apply Units.ext
  change (localEval K w).mapMatrix (singleMatrix K n v g.val) = 1
  rw [eval_singleMatrix, Pi.mulSingle_eq_of_ne h]

theorem localInclusion_injective (v : FinitePlace K) :
    Function.Injective (localInclusion K n v) :=
  Function.LeftInverse.injective (localProjection_localInclusion K n v)

theorem localProjection_surjective (v : FinitePlace K) :
    Function.Surjective (localProjection K n v) :=
  Function.LeftInverse.surjective (localProjection_localInclusion K n v)

theorem isClosedEmbedding_localInclusion (v : FinitePlace K) :
    Topology.IsClosedEmbedding (localInclusion K n v) := by
  let : T2Space (FiniteAdeles K) := inferInstanceAs
    (T2Space (Πʳ w : FinitePlace K, [FiniteCompletion K w, w.adicCompletionIntegers K]))
  exact Function.LeftInverse.isClosedEmbedding (localProjection_localInclusion K n v)
    (localProjection K n v).continuous (localInclusion K n v).continuous

/-- The local projections jointly distinguish adelic matrix units. -/
theorem ext_localProjection {g h : FiniteAdelicGL K n}
    (he : ∀ v, localProjection K n v g = localProjection K n v h) : g = h := by
  apply Units.ext
  apply matrix_ext K n
  intro v
  exact congrArg Units.val (he v)

/-- Matrices supported at distinct places commute, even in noncommutative rank. -/
theorem localInclusion_commute (v w : FinitePlace K) (h : v ≠ w)
    (g : FiniteLocalGL K n v) (g' : FiniteLocalGL K n w) :
    Commute (localInclusion K n v g) (localInclusion K n w g') := by
  change localInclusion K n v g * localInclusion K n w g' =
    localInclusion K n w g' * localInclusion K n v g
  apply ext_localProjection K n
  intro t
  simp only [map_mul]
  by_cases ht : t = v
  · subst t
    rw [localProjection_localInclusion_of_ne K n w v h]
    simp
  · rw [localProjection_localInclusion_of_ne K n v t ht]
    simp

/-- The compact open integral subgroup at an actual finite completion. -/
def localIntegral (v : FinitePlace K) : OpenSubgroup (FiniteLocalGL K n v) :=
  Langlands.GeneralLinearGroup.integralOpenSubgroup (Fin n)
    (v.adicCompletionIntegers K).toSubring
    (Valued.isOpen_valuationSubring (FiniteCompletion K v))

@[simp]
theorem mem_localIntegral (v : FinitePlace K) (g : FiniteLocalGL K n v) :
    g ∈ localIntegral K n v ↔
      (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
      (∀ i j, g⁻¹ i j ∈ v.adicCompletionIntegers K) :=
  Iff.rfl

theorem isCompact_localIntegral (v : FinitePlace K) :
    IsCompact (localIntegral K n v : Set (FiniteLocalGL K n v)) :=
  Langlands.GeneralLinearGroup.isCompact_integralOpenSubgroup (Fin n)
    (v.adicCompletionIntegers K).toSubring
    (Valued.isOpen_valuationSubring (FiniteCompletion K v))
    (isCompact_adicCompletionIntegers K v)

/-- Global integrality is exactly integrality of every local matrix and its inverse. -/
theorem mem_standardIntegral_iff_local (g : FiniteAdelicGL K n) :
    g ∈ standardIntegral K n ↔ ∀ v, localProjection K n v g ∈ localIntegral K n v := by
  simp only [mem_standardIntegral, mem_localIntegral, ← map_inv, localProjection_apply]
  constructor
  · intro h v
    exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩

@[simp]
theorem localInclusion_mem_standardIntegral (v : FinitePlace K) (g : FiniteLocalGL K n v) :
    localInclusion K n v g ∈ standardIntegral K n ↔ g ∈ localIntegral K n v := by
  rw [mem_standardIntegral_iff_local]
  constructor
  · intro h
    simpa only [localProjection_localInclusion] using h v
  · intro h w
    by_cases hw : w = v
    · subst w
      simpa only [localProjection_localInclusion] using h
    · rw [localProjection_localInclusion_of_ne K n v w hw]
      exact (localIntegral K n w).one_mem

theorem comap_standardIntegral_localInclusion (v : FinitePlace K) :
    (standardIntegral K n).toSubgroup.comap (localInclusion K n v).toMonoidHom =
      (localIntegral K n v).toSubgroup := by
  ext g
  exact localInclusion_mem_standardIntegral K n v g

end FiniteAdelicGL

end Langlands.Global
