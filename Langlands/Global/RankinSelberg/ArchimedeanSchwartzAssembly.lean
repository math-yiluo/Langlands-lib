import Langlands.Global.RankinSelberg.ArchimedeanSchwartzTensor
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationStatement
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.PartA

/-! # Assembly of local archimedean Schwartz functions -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

variable (F : Type u) [Field F] [NumberField F]

/-- A local row domain indexed by a real or a complex place. -/
abbrev localRowDomain (n : ℕ) (p :
    {v : InfinitePlace F // v.IsReal} ⊕ {v : InfinitePlace F // v.IsComplex}) : Type :=
  match p with
    | .inl _ => Fin n → ℝ
    | .inr _ => Fin n → ℂ

instance (n : ℕ) (p) : NormedAddCommGroup (localRowDomain F n p) := by
  cases p <;> exact inferInstance

instance (n : ℕ) (p) : NormedSpace ℝ (localRowDomain F n p) := by
  cases p <;> exact inferInstance

/-- Reordering mixed row coordinates into local real and complex rows. -/
def archimedeanRowEquiv (n : ℕ) :
    (Fin n → mixedEmbedding.mixedSpace F) ≃L[ℝ] (p :
      {v : InfinitePlace F // v.IsReal} ⊕ {v : InfinitePlace F // v.IsComplex}) →
        localRowDomain F n p where
  toFun x p := match p with
    | .inl v => fun j => (x j).1 v
    | .inr w => fun j => (x j).2 w
  invFun y j := (fun v => y (.inl v) j, fun w => y (.inr w) j)
  left_inv _ := rfl
  right_inv y := by funext p; cases p <;> rfl
  map_add' _ _ := by funext p; cases p <;> rfl
  map_smul' _ _ := by funext p; cases p <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro p
    cases p <;> apply continuous_pi <;> intro j <;> fun_prop
  continuous_invFun := by fun_prop

/-- The Schwartz external tensor of the local real and complex row functions. -/
def archimedeanTensor (n : ℕ)
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ) :
    SchwartzMap (Fin n → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archimedeanRowEquiv F n)
    (finiteTensor (E := localRowDomain F n) fun p => match p with
      | .inl v => ΦR v
      | .inr w => ΦC w)

@[simp] theorem archimedeanTensor_apply (n : ℕ)
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (x : Fin n → mixedEmbedding.mixedSpace F) :
    archimedeanTensor F n ΦR ΦC x =
      (∏ v, ΦR v (fun j => (x j).1 v)) * ∏ w, ΦC w (fun j => (x j).2 w) := by
  classical
  simp [archimedeanTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    finiteTensor_apply, Fintype.prod_sum_type, archimedeanRowEquiv]

/-- A restricted adelic tensor with prescribed archimedean Schwartz factors. -/
def restrictedTensor (n : ℕ) (S : Finset (FinitePlace F))
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (Φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ) :
    RowVector F n → ℂ :=
  (integralOutside F n S).indicator fun x =>
    archimedeanTensor F n ΦR ΦC (archimedeanCoordinates F n x) *
      ∏ v ∈ S, Φv v (localCoordinates F n v x)

/-- The assembled restricted tensor belongs to the adelic Schwartz–Bruhat space. -/
theorem restrictedTensor_mem_schwartzBruhat (n : ℕ) (S : Finset (FinitePlace F))
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (Φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ)
    (hΦv : ∀ v ∈ S, IsLocallyConstant (Φv v) ∧ HasCompactSupport (Φv v)) :
    restrictedTensor F n S ΦR ΦC Φv ∈ schwartzBruhat F n := by
  apply SchwartzBruhatProof.restricted_le_schwartzBruhat n
  exact Submodule.subset_span ⟨archimedeanTensor F n ΦR ΦC, S, Φv, hΦv, rfl⟩

/-- The assembled restricted tensor is standard at every finite place outside `S`. -/
theorem restrictedTensor_isStandardOutside (n : ℕ) (S : Finset (FinitePlace F))
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (Φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ) :
    IsStandardOutside F n S (restrictedTensor F n S ΦR ΦC Φv) := by
  refine ⟨fun x hx => Set.indicator_of_notMem hx _, ?_⟩
  intro x y hx hy hinf hfin
  change (integralOutside F n S).indicator _ x =
    (integralOutside F n S).indicator _ y
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  have harch : archimedeanCoordinates F n x = archimedeanCoordinates F n y := by
    funext j
    unfold archimedeanCoordinates
    rw [hinf j]
  rw [harch]
  congr 1
  exact Finset.prod_congr rfl fun v hv => congrArg (Φv v) (hfin v hv)

/-- The explicit pointwise factorization, with scalar one and subtype indexing over `S`. -/
theorem restrictedTensor_eq (n : ℕ) (S : Finset (FinitePlace F))
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (Φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ) :
    restrictedTensor F n S ΦR ΦC Φv =
      (integralOutside F n S).indicator fun y =>
        (∏ v, ΦR v (realRowCoordinates F n v y)) *
          (∏ w, ΦC w (complexRowCoordinates F n w y)) *
          ∏ v : S, Φv v.1 (localCoordinates F n v.1 y) := by
  funext y
  by_cases hy : y ∈ integralOutside F n S
  · simp only [restrictedTensor, Set.indicator_of_mem hy, archimedeanTensor_apply]
    have hprod : (∏ v : S, Φv v.1 (localCoordinates F n v.1 y)) =
        ∏ v ∈ S, Φv v (localCoordinates F n v y) :=
      Finset.prod_coe_sort S (fun v => Φv v (localCoordinates F n v y))
    rw [hprod]
    rfl
  · simp only [restrictedTensor, Set.indicator_of_notMem hy]

end Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor
