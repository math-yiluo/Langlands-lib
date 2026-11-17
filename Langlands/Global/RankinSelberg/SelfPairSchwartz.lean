import Langlands.Global.RankinSelberg.SchwartzBruhatProof.PartA
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Nonnegative adelic Schwartz functions standard outside a finite set -/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open SchwartzBruhatProof

variable {F : Type u} [Field F] [NumberField F]

/-- Every adelic row is integral outside some finite set of finite places. -/
theorem exists_integralOutside (n : ℕ) (y : RowVector F n) :
    ∃ S : Finset (FinitePlace F), y ∈ integralOutside F n S := by
  classical
  have h : ∀ᶠ v in Filter.cofinite,
      ∀ j, localCoordinates F n v y j ∈ v.adicCompletionIntegers F := by
    apply Filter.eventually_all.mpr
    intro j
    exact ((y 0 j).2).property
  let bad := Filter.eventually_cofinite.mp h
  refine ⟨bad.toFinset, fun v hv j => ?_⟩
  have hp : ∀ j, localCoordinates F n v y j ∈ v.adicCompletionIntegers F :=
    Classical.byContradiction fun hn => hv (bad.mem_toFinset.mpr hn)
  exact hp j

/-- At an adelic row integral outside `S`, there is a real nonnegative
Schwartz--Bruhat function standard outside `S` with value one at that row. -/
theorem exists_nonnegative_standardSchwartz_of_mem {n : ℕ}
    {S : Finset (FinitePlace F)} {y : RowVector F n}
    (hy : y ∈ integralOutside F n S) :
    ∃ Φ : RowVector F n → ℝ,
      (fun x => (Φ x : ℂ)) ∈ schwartzBruhat F n ∧
      IsStandardOutside F n S (fun x => (Φ x : ℂ)) ∧
      (∀ x, 0 ≤ Φ x) ∧ Φ y = 1 := by
  classical
  obtain ⟨G, -, hGc, hGs, hGr, hGy⟩ :=
    exists_contDiff_tsupport_subset
      (E := Fin n → mixedEmbedding.mixedSpace F)
      (s := Set.univ) (x := archimedeanCoordinates F n y) (n := ⊤) Filter.univ_mem
  have hGnonneg : ∀ z, 0 ≤ G z := fun z => (hGr ⟨z, rfl⟩).1
  have hGcc : HasCompactSupport (Complex.ofRealCLM ∘ G) := hGc.comp_left rfl
  let Gs : SchwartzMap (Fin n → mixedEmbedding.mixedSpace F) ℂ :=
    hGcc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hGs)
  have hGsval (z) : Gs z = (G z : ℂ) := rfl
  let a := finiteCoordinates F n y
  let condition (x : RowVector F n) : Prop :=
    finiteCoordinates F n x - a ∈ latticeVec n (0 : FinitePlace F →₀ ℤ)
  have hcondition (x : RowVector F n) : condition x ↔
      ∀ v j, localCoordinates F n v x j - localCoordinates F n v y j ∈
        v.adicCompletionIntegers F := by
    simp only [condition, mem_latticeVec, mem_finiteLattice, Finsupp.zero_apply]
    constructor
    · intro h v j
      exact (Hecke.mem_additiveLattice_zero_iff v _).mp (h j v)
    · intro h j v
      exact (Hecke.mem_additiveLattice_zero_iff v _).mpr (h v j)
  let Φ : RowVector F n → ℝ :=
    fun x => if condition x then G (archimedeanCoordinates F n x) else 0
  have hΦ (x : RowVector F n) :
      (Φ x : ℂ) = Gs (archimedeanCoordinates F n x) *
        cosetIndicator (latticeVec n (0 : FinitePlace F →₀ ℤ)) a
          (finiteCoordinates F n x) := by
    by_cases hx : condition x <;>
      simp only [Φ, hx, ite_true, ite_false, hGsval, cosetIndicator,
        show (finiteCoordinates F n x - a ∈ latticeVec n 0) = condition x from rfl,
        mul_one, mul_zero, Complex.ofReal_zero]
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · refine Submodule.subset_span ⟨Gs, _, isLocallyConstant_cosetIndicator _
        (isOpen_latticeVec n 0) a,
      hasCompactSupport_cosetIndicator _ (isOpen_latticeVec n 0)
        (isCompact_latticeVec n 0) a, funext hΦ⟩
  · constructor
    · intro x hx
      have hc : ¬ condition x := by
        intro h
        apply hx
        intro v hv j
        have hz := add_mem ((hcondition x).mp h v j) (hy v hv j)
        simpa only [sub_add_cancel] using hz
      simp only [Φ, hc, ite_false, Complex.ofReal_zero]
    · intro x z hx hz harch hloc
      have hc : condition x ↔ condition z := by
        rw [hcondition, hcondition]
        constructor <;> intro h v j <;> by_cases hv : v ∈ S
        · rw [← congrFun (hloc v hv) j]
          exact h v j
        · exact sub_mem (hz v hv j) (hy v hv j)
        · rw [congrFun (hloc v hv) j]
          exact h v j
        · exact sub_mem (hx v hv j) (hy v hv j)
      have ha : archimedeanCoordinates F n x = archimedeanCoordinates F n z := by
        funext j
        exact congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (harch j)
      change ((if condition x then G (archimedeanCoordinates F n x) else 0 : ℝ) : ℂ) =
        ((if condition z then G (archimedeanCoordinates F n z) else 0 : ℝ) : ℂ)
      rw [ha, hc]
  · intro x
    dsimp only [Φ]
    split_ifs
    · exact hGnonneg _
    · exact le_rfl
  · have hc : condition y := by
      change finiteCoordinates F n y - finiteCoordinates F n y ∈ latticeVec n 0
      rw [sub_self]
      exact zero_mem _
    simp only [Φ, hc, ite_true, hGy]

/-- Internal positive test-function existence statement, allowing a finite
exceptional set to be chosen along with the test function. -/
def PositiveStandardSchwartzStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (y : RowVector K n),
    ∃ (S : Finset (FinitePlace K)) (Φ : RowVector K n → ℝ),
      (fun x => (Φ x : ℂ)) ∈ schwartzBruhat K n ∧
      IsStandardOutside K n S (fun x => (Φ x : ℂ)) ∧
      (∀ x, 0 ≤ Φ x) ∧ Φ y = 1

/-- A nonnegative adelic test function with value one at any prescribed row. -/
theorem positiveStandardSchwartz : PositiveStandardSchwartzStatement.{u} := by
  intro K _ _ n y
  obtain ⟨S, hS⟩ := exists_integralOutside n y
  obtain ⟨Φ, hΦ⟩ := exists_nonnegative_standardSchwartz_of_mem hS
  exact ⟨S, Φ, hΦ⟩

end Langlands.Global.RankinSelbergGlobal.SelfPair
